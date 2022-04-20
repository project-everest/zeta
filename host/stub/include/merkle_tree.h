#pragma once
#include <zeta_config.h>
#include <zeta_traits.h>
#include <common.h>
#include <crypt_hash.h>
#include <key.h>
#include <stdlib.h>
#include <stddef.h>
#include <utility>
#include <vector>

namespace Zeta
{

namespace internal
{
    class MerkleValue
    {
    public:

        // Get descendant key along a direction
        virtual BaseKey DescKey (DescDir dir) const = 0;

        // get desc hash value
        virtual const HashValue& DescHashValue (DescDir dir) const = 0;

        // get desc updatable hash value reference
        virtual HashValue& DescHashValue (DescDir dir) = 0;

        // is the desc in blum
        virtual bool IsDescInBlum (DescDir dir) const = 0;

        // set the inBlum value for the descendant
        virtual void SetDescInBlum (DescDir dir, bool isInBlum) = 0;

        // Get the hash of this value
        virtual void GetHashValue (HashValue& hashBuf) const = 0;
    };

    // Forward decl of MerkleTree impl for pimpl
    class MerkleTreeImpl;

    class MerkleTree
    {
    public:


        MerkleTree();
        ~MerkleTree();

        void Put (const BaseKey& key, const MerkleValue& value);
        MerkleValue& Get (const BaseKey& key);

    private:
        MerkleTreeImpl* pimpl_;
    };

    // Extension of a MerkleNode;
    // For performance we want to keep MerkleNode limited to
    // 64 bytes - all overflow state is stored in this struct
    // and pointed to from MerkleNode
    struct alignas(32) MerkleNodeExt
    {
        MerkleNodeExt()
            : dhash { }
            , lastEvictTime { 0 }
            , blumIdx (-1)
            , lastTouchEpoch(InvalidEpochId)
        {

        }

        HashValue dhash[2];      // 64 bytes
        Timestamp lastEvictTime; // 8 bytes  Last evict timestamp (for blum evicted nodes)
        int blumIdx;             // 4 bytes
        EpochId lastTouchEpoch;  // 2 bytes
    };

    struct alignas(CacheAlign) MerkleNode
    {
        MerkleNode(const UInt256& _path, uint16_t _depth, MerkleNodeExt* _ext)
            : path { _path }
            , depth { _depth }
            , status { MerkleNodeStatus::InMerkle }
            , unused (0)
            , cacheIdx { InvalidVCacheIdx }
            , dHashUpdated { }
            , desc { }
            , ext { _ext }
        {
            assert(ext != nullptr);
        }

        const InternalKey& GetKey() const
        {
            return reinterpret_cast<const InternalKey&>(path);
        }

        bool IsEvicted() const
        {
            return status != MerkleNodeStatus::InMerkle;
        }

        bool IsEvictedToBlum() const
        {
            return status == MerkleNodeStatus::InBlum;
        }

        void SetCached(VCacheIdx idx)
        {
            assert(status == MerkleNodeStatus::InMerkle);
            cacheIdx = idx;
            status = MerkleNodeStatus::InCache;
        }

        void ClearCached()
        {
            cacheIdx = InvalidVCacheIdx;
            status = MerkleNodeStatus::InMerkle;
        }

        void SetEvictedToBlum(Timestamp timestamp = 0)
        {
            assert(status == MerkleNodeStatus::InMerkle);
            status = MerkleNodeStatus::InBlum;
            ext->lastEvictTime = timestamp;
        }

        void ClearEvictedToBlum()
        {
            status = MerkleNodeStatus::InMerkle;
        }

        void GetHashValue(Hasher &hasher, HashValue &hashBuf) const
        {
            assert(desc[0] != nullptr);
            assert(desc[1] != nullptr);

            static const uint8_t TagMerkle = 0;
            hasher.HashPartialT(TagMerkle);

            static const uint8_t TagSome = 1;
            hasher.HashPartialT(TagSome);

            hasher.HashPartialT(desc[0]->GetKey());
            hasher.HashPartialT(ext->dhash[0]);
            hasher.HashPartialT(desc[0]->IsEvictedToBlum());

            hasher.HashPartialT(desc[1]->GetKey());
            hasher.HashPartialT(ext->dhash[1]);
            hasher.HashPartialT(desc[1]->IsEvictedToBlum());

            hasher.HashFinal(hashBuf);
        }

#ifdef TRACE_MODE
        std::string GetFormattedSelf() const
        {
            auto left = (desc[0] == nullptr) ?
                "EMPTY" :
                fmt::format("{},{}", desc[0]->GetAddr().GetFormattedSelf(),
                            ext->dhash[0].GetFormattedSelf());

            auto right = (desc[1] == nullptr) ?
                "EMPTY" :
                fmt::format("{},{}",
                            desc[1]->GetAddr().GetFormattedSelf(),
                            ext->dhash[1].GetFormattedSelf());

            return fmt::format("MIT[{}]:({}|{})", GetAddr().GetFormattedSelf(), left, right);
        }

#endif

        UInt256 path;             // 32 bytes
        uint16_t depth;           //  2 bytes
        MerkleNodeStatus status;  // 1 byte
        uint8_t unused;           // 1 byte
        VCacheIdx cacheIdx;       //  2 bytes
        bool dHashUpdated[2];     //  2 bytes
        MerkleNode* desc[2];       // 16 bytes
        MerkleNodeExt* const ext;  // 8 bytes
    };

    struct MerkleTreePathInfo
    {
        MerkleNode* lastCachedNode;
        MerkleNode* lastAncestor;
        MerkleNode* newInternalNode;
        MerkleNode* newLeafNode;
        int pathLen;
        // TODO: Is this correct? what if the path is 256 bits long?
        uint32_t pathDir;
        uint8_t newDir;
    };

    class MerkleTree
    {
    public:
        static_assert(sizeof(MerkleNode) == 64);

        MerkleTree()
            : root_{UInt256{}, 0, nodeExtAllocator_.New(1)}
            , ancPredictor_{}
        {

        }

        ~MerkleTree();

        MerkleTreePathInfo GetPathInfo(const Addr& leafAddr)
        {
            auto predictedAncDepth = ancPredictor_.PredictAncestorDepth(leafAddr);
            auto startAncNode = cachedNodeCache_.Lookup(leafAddr, predictedAncDepth);

            if (nullptr == startAncNode || !startAncNode->IsEvicted())
            {
                startAncNode = &root_;
            }

            auto pathInfo = GetPathInfo(leafAddr, startAncNode);
            if (pathInfo.lastCachedNode != nullptr)
            {
                ancPredictor_.RecordCachedAncestor(leafAddr, pathInfo.lastCachedNode);
            }

            return pathInfo;
        }

        MerkleTreePathInfo GetPathInfo(const Addr &leafAddr, MerkleNode *curNode)
        {
            MerkleTreePathInfo pathInfo = {nullptr, nullptr, nullptr, nullptr, 0, 0};
            auto leafAddrBytes = leafAddr.Bytes();

            // byte index of parentDepth
            auto bi = 0;
            uint64_t dir = 0;

            while (curNode != nullptr)
            {
                INCR_STAT(0, MTTraversals);

                auto curPathBytes = curNode->path.Bytes();
                auto nextDepth = curNode->depth;

                // byte index of currentDepth
                auto cbi = nextDepth >> 6;
                assert(bi <= cbi);
                assert(cbi <= 4);
                assert(bi < 4);

                while (bi < cbi)
                {
                    if (leafAddrBytes[bi] != curPathBytes[bi])
                    {
                        auto s = __builtin_clzll(leafAddrBytes[bi] ^ curPathBytes[bi]);
                        auto newNodeDepth = (bi << 6) + s;
                        pathInfo.newInternalNode = NewNode(leafAddr, newNodeDepth);
                        pathInfo.newLeafNode = NewLeafNode(leafAddr);
                        pathInfo.newDir = (leafAddrBytes[bi] >> (63 - s)) & 1ull;
                        pathInfo.newInternalNode->desc[pathInfo.newDir] = pathInfo.newLeafNode;
                        return pathInfo;
                    }

                    bi++;
                }

                if (4 == bi)
                {
                    assert(curNode->GetAddr() == MerkleAddr::GetLeafAddr(leafAddr));
                    return pathInfo;
                }

                auto cbs = nextDepth & 0x3f;
                if (leafAddrBytes[bi] != curPathBytes[bi])
                {
                    auto s = __builtin_clzll(leafAddrBytes[bi] ^ curPathBytes[bi]);
                    if (cbs > s)
                    {
                        pathInfo.newInternalNode = NewNode(leafAddr, (bi << 6) + s);
                        pathInfo.newLeafNode = NewLeafNode(leafAddr);
                        pathInfo.newDir = (leafAddrBytes[bi] >> (63 - s)) & 1ull;
                        pathInfo.newInternalNode->desc[pathInfo.newDir] = pathInfo.newLeafNode;
                        return pathInfo;
                    }
                }

                if (curNode->IsEvicted())
                {
                    pathInfo.lastCachedNode = curNode;
                    pathInfo.pathLen = 0;
                    pathInfo.pathDir = 0;
                }
                pathInfo.lastAncestor = curNode;

                dir = (leafAddrBytes[bi] >> (63 - cbs)) & 1ull;
                assert(dir <= 1);
                pathInfo.pathDir |= (dir << pathInfo.pathLen);
                pathInfo.pathLen++;

                curNode = curNode->desc[dir];
            }

            assert(curNode == nullptr);
            assert(pathInfo.pathLen == 1);
            pathInfo.newLeafNode = NewLeafNode(leafAddr);

            return pathInfo;
        }

        MerkleNode* GetRoot()
        {
            return &root_;
        }

        void Update(const Addr &leafAddr, const MerkleTreePathInfo &pathInfo)
        {
            assert(pathInfo.pathLen > 0);
            auto dir = (pathInfo.pathDir >> (pathInfo.pathLen - 1)) & 0x01;
            assert(dir <= 1);

            if (pathInfo.newInternalNode != nullptr)
            {
#ifndef NDEBUG
                const auto &newIntAddr = pathInfo.newInternalNode->GetAddr();
                const auto &newLeafAddr = pathInfo.newLeafNode->GetAddr();
                const auto &lastAncAddr = pathInfo.lastAncestor->GetAddr();
                const auto &prevDescAddr = pathInfo.lastAncestor->desc[dir]->GetAddr();
#endif
                assert(pathInfo.newLeafNode != nullptr);
                assert(lastAncAddr.IsAncestor(newIntAddr));
                assert(dir == DescDirTr::ToByte(lastAncAddr.GetDescDir(newIntAddr)));
                assert(newIntAddr.IsAncestor(newLeafAddr));
                assert(newIntAddr.IsAncestor(prevDescAddr));
                assert(pathInfo.newDir < 2);
                assert(pathInfo.newDir == DescDirTr::ToByte(newIntAddr.GetDescDir(newLeafAddr)));
                assert(pathInfo.newInternalNode->desc[pathInfo.newDir] == pathInfo.newLeafNode);

                auto otherDir = 1 - pathInfo.newDir;

                assert(otherDir == DescDirTr::ToByte(newIntAddr.GetDescDir(prevDescAddr)));

                pathInfo.newInternalNode->desc[otherDir] = pathInfo.lastAncestor->desc[dir];
                pathInfo.newInternalNode->ext->dhash[otherDir] = pathInfo.lastAncestor->ext->dhash[dir];
                pathInfo.newInternalNode->dHashUpdated[otherDir] = pathInfo.lastAncestor->dHashUpdated[dir];

                pathInfo.lastAncestor->desc[dir] = pathInfo.newInternalNode;
                pathInfo.lastAncestor->dHashUpdated[dir] = false;
            }
            else if (pathInfo.newLeafNode != nullptr)
            {
                pathInfo.lastAncestor->desc[dir] = pathInfo.newLeafNode;
            }
        }

        void Update(const Addr& leafAddr)
        {
            Update(leafAddr, GetPathInfo(leafAddr));
        }

        void SetCached(MerkleNode* node, VCacheIdx idx)
        {
            node->SetCached(idx);
            cachedNodeCache_.Add(node);
        }

        void ClearCached(MerkleNode* node)
        {
            node->ClearCached();
        }

    private:

        MerkleNode* NewLeafNode(const Addr& path)
        {
            auto d = MerkleAddr::LeafDepth;
            return nodeAllocator_.New(1, path, d, nodeExtAllocator_.New(1));
        }

        MerkleNode* NewNode(const Addr& path, uint16_t depth)
        {
            auto merkleNode =  nodeAllocator_.New(1, path, depth, nodeExtAllocator_.New(1));
            merkleNode->path.ZeroSuffix(MerkleAddr::LeafDepth - depth);
            assert(merkleNode->GetAddr().IsNormalized());
            return merkleNode;
        }

        MerkleNode root_;
    };

} // namespace detail

} // namespace srv

} // namespace Veritas
