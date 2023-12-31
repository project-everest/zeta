#include "zeta_config.h"
#include <assert.h>
#include <formats.h>
#include <stdexcept>
#include <trace.h>
#include <verifier_stub.h>
#include <verifier_stub_impl.h>
#include <zeta_traits.h>

namespace Zeta
{
    VerifierStub::VerifierStub (ThreadId threadId, VerifierProxy verifierProxy)
        : pimpl_ { new VerifierStubImpl (threadId, verifierProxy) }
    {

    }

    VerifierStub::~VerifierStub ()
    {

    }

    Timestamp VerifierStub::Run (AppTransFn* fn)
    {
        return pimpl_->Run(fn);
    }

    void VerifierStub::Flush()
    {
        return pimpl_->Flush();
    }

    EpochId VerifierStub::Verify()
    {
        return pimpl_->Verify();
    }

    Timestamp VerifierStubImpl::Run(AppTransFn* fn)
    {
        assert (fn != nullptr);
        assert (fn->GetArity() >= 0);

        SlotId slots [MaxArity];

        for (int i = 0 ; i < fn->GetArity() ; ++i) {
            slots[i] = EnsureRecordInStore(fn->GetRecord(i));
        }

        LogTransFn(fn, slots);

        if (fn->HasOutput()) {
            RegisterForCallback(fn);
        }

        for (int i = fn->GetArity() - 1 ; i >= 0 ; --i) {

            auto s = slots[i];
            assert (!slotInfo_[s].touched);

            if (fn->Touches(i)) {
                auto ps = slotInfo_[s].parentSlot;
                UpdateMerkleHash(fn->GetRecord(i).GetKey(), fn->GetPostValue(i), slotInfo_[ps].baseKey);
                slotInfo_[ps].touched = true;
            }

            EvictSlot (slots[i]);
        }

        return 0;
    }

    void VerifierStubImpl::Flush()
    {
        FlushImpl();
    }

    EpochId VerifierStubImpl::Verify()
    {
        return 0;
    }

    VerifierStubImpl::VerifierStubImpl (ThreadId threadId, VerifierProxy verifierProxy)
        : threadId_ { threadId }
        , verifierProxy_ { verifierProxy }
        , merkleTree_ { }
        , writeLog_ { }
        , toCallback_ { }
        , outBuf_ { new uint8_t [OutBufSize] }
    {
        // the current code assumes single verifier thread
        static_assert (ThreadCount == 1, "The current code assumes single verifier thread");
        static_assert (StoreSize > 0, "Verifier store size cannot be zero");

        assert (threadId < ThreadCount);

        InitSlots();
        InitMerkleTree();
        assert (ValidStoreInvariants());
    }

    SlotId VerifierStubImpl::EnsureRecordInStore(const AppRecord& record)
    {
        // all store invariants valid at entry
        assert (ValidStoreInvariants());

        auto leafKey = record.GetKey().GetBaseKey();
        auto curKey = BaseKey::Root;
        auto prevSlot = InvalidSlotId;

        while (curKey != leafKey)
        {
            assert (curKey.IsAncestor(leafKey));

            // unless curKey is root, we have the proving ancestor of curKey
            // already in store at slot prevSlot
            assert (curKey == BaseKey::Root ||
                    IsValidSlot(prevSlot) && slotInfo_[prevSlot].baseKey.IsAncestor(curKey));

            // curkey is in the merkle tree
            auto curValue = merkleTree_.Get(curKey);
            assert (curValue != nullptr);

            SlotId curSlot = InvalidSlotId;
            if (!IsInStore(curKey, &curSlot)) {
                curSlot = NewSlotId(curKey, prevSlot);
                LogAddMInternal(curKey, curValue, curSlot, prevSlot);
            }
            prevSlot = curSlot;

            auto dir = DescDirTr::ToByte(curKey.GetDescDir(leafKey));

            if (!curValue->descInfo[dir].isNonNull) {
                AddMerkleTreeEdge(curKey, leafKey);
                break;
            }

            auto& nextKey = curValue->descInfo[dir].key;

            if (!nextKey.IsAncestor(leafKey)) {
                auto newKey = SplitMerkleTreeEdge(curKey, leafKey);
                auto newVal = MerkleValue{};
                auto curSlot = NewSlotId(newKey, prevSlot);
                LogAddMInternal(newKey, &newVal, curSlot, prevSlot);
                prevSlot = curSlot;
                break;
            }

            curKey = nextKey;
        }

        assert (prevSlot != InvalidSlotId);
        auto recSlot = NewSlotId(leafKey, prevSlot);
        LogAddMApp(record, recSlot, prevSlot);

        // all store invariants valid at exit
        assert (ValidStoreInvariants());

        return recSlot;
    }

    void VerifierStubImpl::EvictSlot(SlotId s)
    {
        assert (s + 1 == nextFreeSlot_);
        assert (s > 0);
        assert (IsValidSlot(s));

        auto ps = slotInfo_[s].parentSlot;

        LogEvictM(s, ps);

        if (slotInfo_[s].touched) {
            assert (slotInfo_[s].baseKey.GetDepth() < BaseKey::LeafDepth);
            auto key = slotInfo_[s].baseKey;
            auto value = merkleTree_.Get(key);
            UpdateMerkleHash(key, value, slotInfo_[ps].baseKey);
            slotInfo_[ps].touched = true;
        }

        FreeSlot(s);

        if (ps == s - 1 && ps > 0)
        {
            EvictSlot(ps);
        }
    }

    void VerifierStubImpl::RegisterForCallback(AppTransFn *fn)
    {
        toCallback_.push(fn);
    }

    void VerifierStubImpl::UpdateMerkleHash(const AppKey& key, const AppValue& value, const BaseKey& provingAncestor)
    {
        auto ancValue = merkleTree_.Get(provingAncestor);
        auto baseKey = key.GetBaseKey();

        assert (ancValue != nullptr);
        assert (provingAncestor.IsAncestor(baseKey));
        assert (provingAncestor.GetDepth() < baseKey.GetDepth());

        auto dir = DescDirTr::ToByte(provingAncestor.GetDescDir(baseKey));
        assert (ancValue->descInfo[dir].key == baseKey);
        Formats::GetHashValue(value, ancValue->descInfo[dir].hash);
    }

    void VerifierStubImpl::UpdateMerkleHash(const BaseKey& key, const MerkleValue* value, const BaseKey& provingAncestor)
    {
        auto ancValue = merkleTree_.Get(provingAncestor);
        assert (ancValue != nullptr);

        assert (provingAncestor.IsAncestor(key));
        assert (provingAncestor.GetDepth() < key.GetDepth());

        auto dir = DescDirTr::ToByte(provingAncestor.GetDescDir(key));
        assert (ancValue->descInfo[dir].key == key);
        Formats::GetHashValue(value, ancValue->descInfo[dir].hash);
    }

    static void RaiseException (int rc)
    {
        switch (rc) {
        case VRC_VerificationFailure: throw VerificationFailureException();
        case VRC_AppFailure: throw VerifierAppFailure();
        case VRC_EntryFailure: throw VerifierEntryFailure();
        case VRC_ParsingFailure: throw VerifierParsingFailure();
        default:
            throw std::runtime_error("invalid return code");
        }
    }

    void VerifierStubImpl::FlushImpl()
    {
        if (writeLog_.Written() > 0) {
            size_t outSize = 0;

            TRACE_DEBUG("Thread{}: Verifying a log of size {}", threadId_, writeLog_.Written());

            auto rc = verifierProxy_.VerifyLog(threadId_,
                                               const_cast<uint8_t*>(writeLog_.Bytes()),
                                               writeLog_.Written(),
                                               outBuf_.get(),
                                               OutBufSize,
                                               &outSize);
            TRACE_DEBUG("Return code: {}, Output size: {}", rc, outSize);

            assert (rc == VRC_VerificationFailure ||
                    rc == VRC_ParsingFailure ||
                    rc == VRC_AppFailure ||
                    rc == VRC_EntryFailure ||
                    rc == VRC_Success);

            if (rc != VRC_Success) {
                RaiseException(rc);
            }

            auto outLog = ReadLog { outBuf_.get(), outSize };

            // Output callbacks
            for ( ; !toCallback_.empty() ; toCallback_.pop()) {
                auto fn = toCallback_.front();
                assert (fn->HasOutput());
                fn->SetOutput(outLog);
           }
        }

        writeLog_.Clear();
    }

    void VerifierStubImpl::InitSlots()
    {
        slotInfo_[0].baseKey = BaseKey::Root;
        slotInfo_[0].parentSlot = InvalidSlotId;

        for (SlotId s = 0 ; s < StoreSize ; ++s) {
            slotInfo_[s].touched = false;
        }

        nextFreeSlot_ = 1;
    }

    bool VerifierStubImpl::IsInStore(const BaseKey& baseKey, SlotId* slot)
    {
        assert (slot != nullptr);

        for (SlotId s = 0 ; s < nextFreeSlot_ ; ++s) {
            if (slotInfo_[s].baseKey == baseKey) {
                *slot = s;
                return true;
            }
        }

        *slot = InvalidSlotId;
        return false;
    }

    SlotId VerifierStubImpl::NewSlotId(const BaseKey& key, SlotId parentSlot)
    {
        if (nextFreeSlot_ == StoreSize) {
            // TODO: throw
        }

        auto s = nextFreeSlot_++;
        assert (!slotInfo_[s].touched);

        slotInfo_[s].baseKey = key;
        slotInfo_[s].parentSlot = parentSlot;

        return s;
    }

    void VerifierStubImpl::FreeSlot(SlotId s)
    {
        assert (s + 1 == nextFreeSlot_ && s > 0);

        slotInfo_[s].touched = false;
        nextFreeSlot_--;
    }

#ifdef DEBUG

    bool VerifierStubImpl::IsValidSlot(SlotId s) const
    {
        return (s >= 0 && s < nextFreeSlot_);
    }

#define CHECK(x) if (!(x)) return false;

    bool VerifierStubImpl::ValidStoreInvariants() const
    {
        // root is always in the store at slot id 0
        CHECK(nextFreeSlot_ > 0 && nextFreeSlot_ <= StoreSize);

        CHECK (slotInfo_[0].baseKey == BaseKey::Root);
        CHECK (slotInfo_[0].parentSlot == InvalidSlotId);

        for (SlotId s = 1 ; s < nextFreeSlot_ ; ++s)
        {
            auto ps = slotInfo_[s].parentSlot;
            CHECK(ps < s);
            CHECK(slotInfo_[ps].baseKey.IsAncestor(slotInfo_[s].baseKey));
        }

        for (SlotId s = nextFreeSlot_ ; s < StoreSize ; ++s) {
            CHECK(slotInfo_[s].touched == false);
        }

        return true;
    }

#endif

    static const int MaxLogEntrySize = (1 << 16);

    void VerifierStubImpl::EnsureEnoughLogSpace()
    {
        if (writeLog_.LeftToWrite() < MaxLogEntrySize) {
            FlushImpl();
        }

        assert (writeLog_.LeftToWrite() > MaxLogEntrySize);
    }

    void VerifierStubImpl::LogTransFn (const AppTransFn* fn, const SlotId* slots)
    {
        EnsureEnoughLogSpace();
        Formats::LogRunApp(fn->GetId(), fn->GetArity(), fn->GetParam(), slots, writeLog_);
    }

    void VerifierStubImpl::LogAddMInternal (const BaseKey& key, const MerkleValue* value, SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogAddMInternal(key, value, s, ps, writeLog_);
        FlushImpl();
    }

    void VerifierStubImpl::LogAddMApp (const AppRecord& record, SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogAddMApp(record, s, ps, writeLog_);
        FlushImpl();
    }

    void VerifierStubImpl::LogEvictM (SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogEvictM(s, ps, writeLog_);
        FlushImpl();
    }

    void VerifierStubImpl::InitMerkleTree()
    {
        merkleTree_.Put(BaseKey::Root);
    }

    void VerifierStubImpl::AddMerkleTreeEdge(const BaseKey& anc, const BaseKey& desc)
    {
        // we can prove that new edges are added only to the root node
        assert (anc.IsRoot());

        // a leaf basekey always triggers adding/splitting merkle tree edges
        assert(desc.GetDepth() == BaseKey::LeafDepth);

        auto mv = merkleTree_.Get(anc);
        assert (mv != nullptr);

        assert(anc.IsAncestor(desc));
        auto dir = DescDirTr::ToByte(anc.GetDescDir(desc));
        assert (dir < 2);

        assert (!mv->descInfo[dir].isNonNull);
        mv->descInfo[dir].isNonNull = true;
        mv->descInfo[dir].key = desc;
        mv->descInfo[dir].inBlum = false;
    }

    BaseKey VerifierStubImpl::SplitMerkleTreeEdge(const BaseKey& anc, const BaseKey& desc)
    {
        // a leaf basekey always triggers adding/splitting merkle tree edges
        assert(desc.GetDepth() == BaseKey::LeafDepth);

        assert(anc.IsAncestor(desc));

        auto mv = merkleTree_.Get(anc);
        assert (mv != nullptr);

        auto dir = DescDirTr::ToByte(anc.GetDescDir(desc));
        assert (dir < 2);

        assert (mv->descInfo[dir].isNonNull);

        auto& prevDesc = mv->descInfo[dir].key;
        assert (!prevDesc.IsAncestor(desc));

        auto newKey = BaseKey::GetLeastCommonAncestor(desc, prevDesc);
        // newKey is a proper desc of anc and a propert ancestor of desc&prevDesc
        assert (newKey.IsDescendant(anc) && newKey.GetDepth() > anc.GetDepth());
        assert (newKey.IsAncestor(prevDesc) && newKey.GetDepth() < prevDesc.GetDepth());
        assert (newKey.IsAncestor(desc) && newKey.GetDepth() < desc.GetDepth());

        assert (merkleTree_.Get(newKey) == nullptr);
        auto newVal = merkleTree_.Put(newKey);

        // update merkle tree
        auto dir2 = DescDirTr::ToByte(newKey.GetDescDir(desc));
        auto odir2 = 1 - dir2;

        newVal->descInfo[dir2].key = desc;
        newVal->descInfo[dir2].isNonNull = true;
        newVal->descInfo[dir2].inBlum = false;

        newVal->descInfo[odir2].key = mv->descInfo[dir].key;
        newVal->descInfo[odir2].inBlum = mv->descInfo[dir].inBlum;
        newVal->descInfo[odir2].hash = mv->descInfo[dir].hash;
        newVal->descInfo[odir2].isNonNull = true;
        assert (mv->descInfo[dir].isNonNull);

        mv->descInfo[dir].inBlum = false;
        mv->descInfo[dir].key = newKey;

        return newKey;
    }
}
