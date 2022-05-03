#include <assert.h>
#include <verifier_stub.h>
#include <verifier_stub_impl.h>
#include <zeta_traits.h>

namespace Zeta
{

    VerifierStub::VerifierStub (ThreadId threadId)
        : pimpl_ { new VerifierStubImpl (threadId) }
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

        for (int i = 0 ; i < fn->GetArity() ; ++i) {
            EvictRecord (slots[i]);
        }

        if (fn->HasOutput()) {
            RegisterForCallback(fn);
        }

        for (int i = 0 ; i < fn->GetArity() ; ++i) {
            HandleUpdate(fn->GetRecord(i), fn->GetPostValue(i));
        }

        return 0;
    }

    VerifierStubImpl::VerifierStubImpl (ThreadId threadId)
        : merkleTree_ { }
    {
        // the current code assumes single verifier thread
        static_assert (ThreadCount == 1, "The current code assumes single verifier thread");
        static_assert (StoreSize > 0, "Verifier store size cannot be zero");

        assert (threadId < ThreadCount);
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
                    prevSlot < nextFreeSlot_ && slots_[prevSlot].baseKey.IsAncestor(curKey));

            // curkey is in the merkle tree
            auto curValue = merkleTree_.Get(curKey);
            assert (curValue != nullptr);

            SlotId curSlot = InvalidSlotId;
            if (!IsInStore(curKey, &curSlot)) {
                if (nextFreeSlot_ >= StoreSize) {
                    // TODO: throw
                }

                auto curSlot = nextFreeSlot_++;
                LogAddMInternal(curKey, curValue, curSlot, prevSlot);

                slots_[curSlot].baseKey = curKey;
                slots_[curSlot].parentSlot = prevSlot;
            }

            assert (curSlot < nextFreeSlot_);
            assert (slots_[curSlot].baseKey == curKey);
            assert (slots_[curSlot].parentSlot == prevSlot);

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

                if (nextFreeSlot_ >= StoreSize) {
                    // TODO: throw
                }

                auto curSlot = nextFreeSlot_++;
                LogAddMInternal(newKey, newVal, curSlot, prevSlot);

                slots_[curSlot].baseKey = newKey;
                slots_[curSlot].parentSlot = prevSlot;

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

        // all store invariants valid at exit
        assert (ValidStoreInvariants());

        return 0;
    }

#ifdef DEBUG

#define CHECK(x) if (!(x)) return false;

    bool VerifierStubImpl::ValidStoreInvariants() const
    {
        // root is always in the store at slot id 0
        CHECK(nextFreeSlot_ > 0 && nextFreeSlot_ <= StoreSize);

        CHECK (slots_[0].baseKey == BaseKey::Root);
        CHECK (slots_[0].parentSlot == InvalidSlotId);

        for (SlotId s = 1 ; s < nextFreeSlot_ ; ++s)
        {
            auto ps = slots_[s].parentSlot;
            CHECK(ps < s);
            CHECK(slots_[ps].baseKey.IsAncestor(slots_[s].baseKey));
        }

        return true;
    }

#endif


}
