#include <assert.h>
#include <formats.h>
#include <verifier_proxy.h>
#include <verifier_stub.h>
#include <verifier_stub_impl.h>
#include <zeta_traits.h>

namespace Zeta
{
    VerifierStub::VerifierStub (ThreadId threadId, OutCallback outCallback)
        : pimpl_ { new VerifierStubImpl (threadId, outCallback) }
    {

    }

    VerifierStub::~VerifierStub ()
    {

    }

    Timestamp VerifierStub::Run (const TransFn* fn)
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

    Timestamp VerifierStubImpl::Run(const TransFn* fn)
    {
        assert (fn != nullptr);
        assert (fn->GetArity() >= 0);

        SlotId slots [MaxArity];

        for (int i = 0 ; i < fn->GetArity() ; ++i) {
            slots[i] = EnsureRecordInStore(fn->GetRecord(i));
        }

        LogTransFn(fn, slots);

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

        if (fn->HasOutput()) {
            RegisterForCallback(fn);
        }

        return 0;
    }

    void VerifierStubImpl::Flush()
    {
        FlushImpl();
    }

    VerifierStubImpl::VerifierStubImpl (ThreadId threadId, OutCallback outCallback)
        : threadId_ { threadId }
        , outCallback_ {outCallback}
        , merkleTree_ { }
        , writeLog_ { }
    {
        // the current code assumes single verifier thread
        static_assert (ThreadCount == 1, "The current code assumes single verifier thread");
        static_assert (StoreSize > 0, "Verifier store size cannot be zero");

        assert (threadId < ThreadCount);

        InitSlots();

        VerifierProxy::Init();
        assert (ValidStoreInvariants());
    }

    SlotId VerifierStubImpl::EnsureRecordInStore(const Record& record)
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
                auto curSlot = NewSlotId(curKey, prevSlot);
                LogAddMInternal(curKey, curValue, curSlot, prevSlot);
            }

            auto dir = DescDirTr::ToByte(curKey.GetDescDir(leafKey));
            auto& nextKey = curValue->descInfo[dir].key;

            if (nextKey.IsAncestor(leafKey)) {
                prevSlot = curSlot;
                curKey = nextKey;
            }
            else {
                auto newKey = BaseKey::GetLeastCommonAncestor(leafKey, nextKey);
                assert (newKey.IsDescendant(curKey) && newKey.GetDepth() > curKey.GetDepth());
                assert (newKey.IsAncestor(nextKey) && newKey.GetDepth() < nextKey.GetDepth());
                assert (newKey.IsAncestor(leafKey) && newKey.GetDepth() < BaseKey::LeafDepth);

                auto newVal = merkleTree_.Put(newKey);
                auto curSlot = NewSlotId(newKey, prevSlot);

                LogAddMInternal(newKey, newVal, curSlot, prevSlot);

                // update merkle tree
                auto dir2 = DescDirTr::ToByte(newKey.GetDescDir(leafKey));
                auto odir2 = 1 - dir2;

                newVal->descInfo[dir2].key = leafKey;
                newVal->descInfo[odir2].key = newKey;
                newVal->descInfo[odir2].inBlum = curValue->descInfo[dir].inBlum;

                curValue->descInfo[dir].inBlum = false;
                curValue->descInfo[dir].key = newKey;

                prevSlot = curSlot;
                curKey = leafKey;
            }
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
        }

        FreeSlot(s);

        if (ps == s - 1 && ps > 0)
        {
            EvictSlot(ps);
        }
    }

    void VerifierStubImpl::RegisterForCallback(const TransFn *fn)
    {
        toCallback_.push(fn);
    }

    void VerifierStubImpl::UpdateMerkleHash(const Key& key, const Value& value, const BaseKey& provingAncestor)
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

    void VerifierStubImpl::FlushImpl()
    {
        if (writeLog_.Written() > 0) {
            size_t outSize = 0;

            auto rc = VerifierProxy::VerifyLog(threadId_,
                                               writeLog_.Bytes(),
                                               writeLog_.Written(),
                                               outBuf_.get(),
                                               OutBufSize,
                                               &outSize);

            // TODO: handle errors
            assert (rc == VerifierReturnCode::Success);

            auto readLog = ReadLog { outBuf_.get(), outSize };

            // Output callbacks
            for ( ; !toCallback_.empty() ; toCallback_.pop()) {
                auto fn = toCallback_.front();
                auto fnOutSize = readLog.Deserialize<uint32_t>();
                auto fnOut = readLog.DeserializeBuf(fnOutSize);
                outCallback_(fn, fnOut, fnOutSize);
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
        assert (s == nextFreeSlot_ && s > 0);

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

    void VerifierStubImpl::LogTransFn (const TransFn* fn, const SlotId* slots)
    {
        EnsureEnoughLogSpace();
        Formats::LogRunApp(fn->GetId(), fn->GetArity(), fn->GetParam(), slots, writeLog_);
    }

    void VerifierStubImpl::LogAddMInternal (const BaseKey& key, const MerkleValue* value, SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogAddMInternal(key, value, s, ps, writeLog_);
    }

    void VerifierStubImpl::LogAddMApp (const Record& record, SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogAddMApp(record, s, ps, writeLog_);
    }

    void VerifierStubImpl::LogEvictM (SlotId s, SlotId ps)
    {
        EnsureEnoughLogSpace();
        Formats::LogEvictM(s, ps, writeLog_);
    }
}
