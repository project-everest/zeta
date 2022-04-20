//*************************************************************************
//              Copyright (c) Microsoft Corporation.
//
// @File: vmem_mgr_impl.h
// @Owner: arvinda
//
// Purpose:
//
//  Internal implementation class of verified memory manager
//
// @EndHeader@
//*************************************************************************

#pragma once

#include <merkle_tree.h>
#include <srv_cache.h>
#include <srv_stats.h>
#include <utility>
#include <vcellutils.h>
#include <vector>

namespace Veritas
{

namespace srv
{

    //----------------------------------------------------------------------
    // Class: VMemoryManagerImpl
    //
    // Description:
    //   Implementation class of verified memory manager
    //
    template<typename ServerTr>
    class VMemoryManagerImpl<VerificationSchemeT::Merkle, ServerTr>
    {
        using LogStream = typename ServerTr::LogStream;
        using Hasher = typename ServerTr::Hasher;
        using HashValue = typename Hasher::HashValue;
        using VCell = typename ServerTr::VCell;
        static const size_t ValueSize64 = VCell::ValueSize64;
        using AuxInfoRef = typename ServerTr::AuxInfoRef;
        using AuxInfoContext = typename ServerTr::AuxInfoContext;
        using MerkleNode = detail::MerkleNode<ServerTr>;
        using MerkleTree = detail::MerkleTree<ServerTr>;
        using CacheManager = detail::CacheManager<ServerTr::CacheUsePolicy, ServerTr>;
        using Cache = detail::Cache<ServerTr>;

    public:
        VMemoryManagerImpl(ThreadId id,
                          AuxInfoContext auxInfoCtxt, LogStream& logStream,
                          MerkleAddr partitionRoot = MerkleAddr())
            : id_ {id}
            , auxInfoCtxt_ { auxInfoCtxt }
            , logStream_ {logStream}
            , cache_ { }
            , cacheMgr_ { *this }
            , merkleTree_ { partitionRoot }
            , hasher_ { }
            , freeIdx_{InvalidVCacheIdx}
            , idx_{InvalidVCacheIdx}
            , elideAdd_{false}
        {
#ifdef STATS_MODE
            StatMgr::TheInstance().ResetStats();
#endif
            // Add root to cache 0, idx 0
            if (id == 0)
            {
                cache_[0].SetInternal(merkleTree_.GetRoot(), 0);
                merkleTree_.SetCached(merkleTree_.GetRoot(), 0);
                cacheMgr_.Pin(0, 0);
                cacheMgr_.Pin(0, 1);
            }
        }

        ThreadId GetThreadId() const
        {
            return id_;
        }

        LogStream& GetLogStream()
        {
            return logStream_;
        }

        void BeginOperation ()
        {
            cacheMgr_.BeginOperation();
            if (freeIdx_ == InvalidVCacheIdx)
            {
                freeIdx_ = cacheMgr_.GetFreeIndex();
            }
            assert(!elideAdd_);
        }

        Timestamp PrepInit(Timestamp auxInfoCur)
        {
            return PrepAdd(auxInfoCur);
        }

        Timestamp PrepAdd(Timestamp auxInfoCur) {
            if (AuxInfoTr::IsCached(auxInfoCur))
            {
                idx_ = AuxInfoTr::GetCacheIdx(auxInfoCur);
                assert(AuxInfoTr::GetCacheThreadId(auxInfoCur) == 0);
                assert(cache_[idx_].isLeaf);
                elideAdd_ = true;
                return auxInfoCur;
            }

            assert(freeIdx_ != InvalidVCacheIdx);
            assert(!elideAdd_);
            return AuxInfoTr::GetCacheInfo(id_, freeIdx_);
        }

        VCacheIdx InitAdd(const VCell& vcell, AuxInfoRef auxInfoRef)
        {
            return Add(vcell, auxInfoRef);
        }

        VCacheIdx Add (const VCell& vcell, AuxInfoRef auxInfoRef)
        {
            if (elideAdd_) {
                cacheMgr_.Touch(idx_);
                return idx_;
            }

            idx_ = freeIdx_;
            freeIdx_ = InvalidVCacheIdx;

            auto vcAddr = vcell.GetAddr();
            auto [ancIdx, dir] = EnsureMerkleParentInCache(vcAddr);
            cacheMgr_.Pin(ancIdx, dir);
            cache_[idx_].SetLeaf(auxInfoRef, ancIdx);

#ifndef NDEBUG
            assert(!cache_[ancIdx].isLeaf);
            auto merkleNode = cache_[ancIdx].i.merkleNode;
            auto& ancAddr = merkleNode->GetAddr();
            assert(ancAddr.IsAncestor(MerkleAddr::GetLeafAddr(vcAddr)));
            assert(ancAddr.GetDescDir(MerkleAddr::GetLeafAddr(vcAddr)) == static_cast<DescDir>(dir));
            assert(dir < 2);
            assert(cache_[ancIdx].i.descIdx[dir] == InvalidVCacheIdx);
#endif

            cache_[ancIdx].i.descIdx[dir] = idx_;
            TRACE_DEBUG("{}: Adding {} to idx {}", cacheOpIdx_++, vcAddr.GetFormattedSelf(), idx_);
            LogMerkleLeafAdd(idx_, ancIdx, vcell);
            INCR_STAT(id_, Adds);

            return idx_;
        }

        void Update(const VCell& vcell)
        {
            assert(idx_ != InvalidVCacheIdx);
            vcell.SerializeValue(cache_.GetVCellBuf(idx_));
            cache_[idx_].modified = true;
        }

        void EndOperation()
        {
            cacheMgr_.EndOperation();
            idx_ = InvalidVCacheIdx;
            elideAdd_ = false;
        }

        void Discard(Timestamp auxInfoCur)
        {
            elideAdd_ = false;
        }

        void Evict(VCacheIdx idx)
        {
            if (cache_[idx].isLeaf)
            {
                if (cache_[idx].auxInfoRef)
                {
                    auto ancIdx = cache_[idx].ancIdx;
                    assert(!cache_[ancIdx].isLeaf);
                    assert(cache_[ancIdx].i.descIdx[0] == idx ||
                           cache_[ancIdx].i.descIdx[1] == idx);

                    auto di = (cache_[ancIdx].i.descIdx[0] == idx) ? 0 : 1;

                    if (cache_[idx].modified)
                    {
                        HashConstructor<ValueSize64>::GetHash(cache_.GetVCellBuf(idx),
                                                              cache_[ancIdx].i.merkleNode->ext->dhash[di]);
                        cache_[ancIdx].modified = true;
                        TRACE_DEBUG("srv: Updated {}", cache_[ancIdx].i.merkleNode->GetFormattedSelf());
                    }

                    auto &auxRef = cache_[idx].auxInfoRef;
                    DEBUG_ONLY(bool succ = )
                        auxRef.CompareUpdateBool64(auxInfoCtxt_, AuxInfoTr::GetCacheInfo(id_, idx), AuxInfoTr::DefaultNoInfo);
                    assert(succ);

                    cache_[idx].auxInfoRef = AuxInfoRef();
                    TRACE_DEBUG("{}: srv:Cache evict * from slot {}", cacheOpIdx_++, idx);
                    cache_[ancIdx].i.descIdx[di] = InvalidVCacheIdx;
                    cacheMgr_.UnPin(ancIdx, di);
                    LogMerkleEvict(idx, ancIdx);

                    INCR_STAT(id_, Evicts);
                }
            }
            else
            {
                auto ancIdx = cache_[idx].ancIdx;
                assert(!cache_[ancIdx].isLeaf);
                assert(cache_[ancIdx].i.descIdx[0] == idx ||
                       cache_[ancIdx].i.descIdx[1] == idx);

                auto di = (cache_[ancIdx].i.descIdx[0] == idx) ? 0 : 1;
                assert(cache_[ancIdx].i.merkleNode->desc[di] == cache_[idx].i.merkleNode);

                if (cache_[idx].modified)
                {
                    cache_[idx].i.merkleNode->GetHashValue(hasher_, cache_[ancIdx].i.merkleNode->ext->dhash[di]);
                    cache_[ancIdx].modified = true;
                    TRACE_DEBUG("srv: Updated {}", cache_[ancIdx].i.merkleNode->GetFormattedSelf());
                    TRACE_DEBUG("srv: Evicted {}", cache_[idx].i.merkleNode->GetFormattedSelf());
                }
                merkleTree_.ClearCached(cache_[idx].i.merkleNode);

                TRACE_DEBUG("{}: srv:Cache evict {} from slot {}",
                            cacheOpIdx_++,
                            cache_[idx].i.merkleNode->GetAddr().GetFormattedSelf(), idx);
                cache_[ancIdx].i.descIdx[di] = InvalidVCacheIdx;
                cacheMgr_.UnPin(ancIdx, di);
                LogMerkleEvict(idx, ancIdx);

                INCR_STAT(id_, Evicts);
            }
        }

    private:
        void LogMerkleLeafAdd(VCacheIdx idx, VCacheIdx ancIdx, const VCell &vcell)
        {
            static const size_t logEntrySize = 1 + VCell::Size64;
            auto buf = logStream_.GetLogSpace(logEntrySize);

            auto header = reinterpret_cast<uint16_t *>(buf++);
            header[0] = static_cast<uint16_t>(VMemOpId::MerkleLeafAdd);
            header[1] = idx;
            header[2] = ancIdx;

            vcell.Serialize(buf);
            logStream_.Done(logEntrySize);
            ADD_STAT(id_, LogSize, logEntrySize);
        }

        void LogMerkleIntAdd(VCacheIdx idx, VCacheIdx ancIdx, const MerkleNode *merkleNode)
        {
            static const size_t logEntrySize = 18;
            auto buf = logStream_.GetLogSpace(logEntrySize);

            auto header = reinterpret_cast<uint16_t *>(buf++);
            header[0] = static_cast<uint16_t>(VMemOpId::MerkleIntAdd);
            header[1] = idx;
            header[2] = ancIdx;
            header[3] = 0;

            assert(merkleNode->desc[0] != nullptr);
            assert(merkleNode->desc[1] != nullptr);

            auto depths = reinterpret_cast<uint16_t *>(buf++);
            depths[0] = merkleNode->depth;
            depths[1] = merkleNode->desc[0]->depth;
            depths[2] = merkleNode->desc[1]->depth;

            buf = merkleNode->desc[0]->path.Serialize(buf);
            buf = merkleNode->desc[1]->path.Serialize(buf);
            buf = merkleNode->ext->dhash[0].Serialize(buf);
            buf = merkleNode->ext->dhash[1].Serialize(buf);

            logStream_.Done(logEntrySize);
            ADD_STAT(id_, LogSize, logEntrySize);
        }

        void LogMerkleEmptyAdd(VCacheIdx idx, VCacheIdx ancIdx, const MerkleNode *merkleNode)
        {
            static const size_t logEntrySize = 5;
            auto buf = logStream_.GetLogSpace(logEntrySize);

            auto header = reinterpret_cast<uint16_t *>(buf++);
            header[0] = static_cast<uint16_t>(VMemOpId::MerkleEmptyAdd);
            header[1] = idx;
            header[2] = ancIdx;
            header[3] = merkleNode->depth;

            merkleNode->path.Serialize(buf);
            logStream_.Done(logEntrySize);
            ADD_STAT(id_, LogSize, logEntrySize);
        }

        void LogMerkleEvict(VCacheIdx idx, VCacheIdx ancIdx)
        {
            static const size_t logEntrySize = 1;
            auto buf = logStream_.GetLogSpace(logEntrySize);
            auto header = reinterpret_cast<uint16_t *>(buf);
            header[0] = static_cast<uint16_t>(VMemOpId::MerkleEvict);
            header[1] = idx;
            header[2] = ancIdx;

            logStream_.Done(logEntrySize);
            ADD_STAT(id_, LogSize, logEntrySize);
        }

        std::pair<VCacheIdx, uint8_t> EnsureMerkleParentInCache(const Addr &leafPath)
        {
            auto pathInfo = merkleTree_.GetPathInfo(leafPath);

            assert(pathInfo.lastCachedNode != nullptr);
            assert(pathInfo.lastCachedNode->IsEvicted());
            auto idx = pathInfo.lastCachedNode->cacheIdx;
            auto prevNode = pathInfo.lastCachedNode;

            // p+1, .. are all not-cached and need to be added
            auto pathDir = pathInfo.pathDir;

            for (int i = 0; i < pathInfo.pathLen - 1; ++i)
            {
                assert(idx != InvalidVCacheIdx);
                assert(prevNode != nullptr);
                assert(prevNode->cacheIdx == idx);

                auto dir = pathDir & 0x01;
                pathDir >>= 1;

                auto curNode = prevNode->desc[dir];
                assert(curNode != nullptr);
                assert(!curNode->IsEvicted());

                auto ancIdx = idx;
                cacheMgr_.Pin(ancIdx, dir);

                idx = cacheMgr_.GetFreeIndex();
                cache_[idx].SetInternal(curNode, ancIdx);

#ifndef NDEBUG
                assert(!cache_[ancIdx].isLeaf);
                auto &ancAddr = cache_[ancIdx].i.merkleNode->GetAddr();
                assert(ancAddr.IsAncestor(curNode->GetAddr()));
                assert(static_cast<int>(ancAddr.GetDescDir(curNode->GetAddr())) == dir);
#endif

                assert(cache_[ancIdx].i.descIdx[dir] == InvalidVCacheIdx);
                cache_[ancIdx].i.descIdx[dir] = idx;

                merkleTree_.SetCached(curNode, idx);

                TRACE_DEBUG("{}: srv: Adding {} to idx {}", cacheOpIdx_++, curNode->GetFormattedSelf(), idx);
                LogMerkleIntAdd(idx, ancIdx, curNode);

                prevNode = curNode;
                INCR_STAT(id_, Adds);
            }

            auto ldir = pathDir & 0x01;
            if (pathInfo.newInternalNode != nullptr)
            {
                assert(pathInfo.newLeafNode != nullptr);
                assert(idx != InvalidVCacheIdx);
                assert(prevNode != nullptr);
                assert(prevNode->cacheIdx == idx);
                assert(!cache_[idx].isLeaf);
                assert(cache_[idx].i.merkleNode == prevNode);

                auto dir = ldir;
                ldir = pathInfo.newDir;

                auto curNode = pathInfo.newInternalNode;
                assert(!curNode->IsEvicted());

                auto ancIdx = idx;
                bool pinAdded = false;

                if (cache_[ancIdx].i.descIdx[dir] == InvalidVCacheIdx)
                {
                    cacheMgr_.Pin(ancIdx, dir);
                    pinAdded = true;
                }

                idx = cacheMgr_.GetFreeIndex();
                cache_[idx].SetInternal(curNode, ancIdx);

#ifndef NDEBUG
                auto &ancAddr = prevNode->GetAddr();
                assert(ancAddr.IsAncestor(curNode->GetAddr()));
                assert(static_cast<int>(ancAddr.GetDescDir(curNode->GetAddr())) == dir);
#endif

                if (cache_[ancIdx].i.descIdx[dir] != InvalidVCacheIdx)
                {
                    auto descIdx = cache_[ancIdx].i.descIdx[dir];
                    assert(cache_[descIdx].ancIdx == ancIdx);

                    auto ddi = 1 - pathInfo.newDir;
                    assert(ddi == 0 || ddi == 1);

#ifndef NDEBUG
                    auto &descAddr = prevNode->desc[dir]->GetAddr();
                    assert(curNode->GetAddr().IsAncestor(descAddr));
                    auto ddir = curNode->GetAddr().GetDescDir(descAddr);
                    assert(ddi == DescDirTr::ToByte(ddir));
#endif

                    cache_[idx].i.descIdx[ddi] = descIdx;
                    cache_[descIdx].ancIdx = idx;
                    cacheMgr_.Pin(idx, ddi);
                }
                else if (!pinAdded)
                {
                    cacheMgr_.Pin(ancIdx, dir);
                }

                cache_[ancIdx].i.descIdx[dir] = idx;
                merkleTree_.SetCached(curNode, idx);

                TRACE_DEBUG("{}: srv: Adding {} to idx {}", cacheOpIdx_++, curNode->GetFormattedSelf(), idx);
                LogMerkleEmptyAdd(idx, ancIdx, curNode);
                INCR_STAT(id_, Adds);
            }

            merkleTree_.Update(leafPath, pathInfo);

            return std::make_pair(idx, ldir);
        }

        const ThreadId id_;
        const AuxInfoContext auxInfoCtxt_;
        LogStream& logStream_;
        Cache cache_;
        CacheManager cacheMgr_;
        MerkleTree merkleTree_;
        Hasher hasher_;
        VCacheIdx freeIdx_;
        VCacheIdx idx_;
        bool elideAdd_;

#ifdef TRACE_MODE
        int cacheOpIdx_ = 0;
#endif

    };

} // namespace Server

} // namespace Veritas
