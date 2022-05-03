#pragma once

#include <app.h>
#include <common.h>
#include <merkle_tree.h>

namespace Zeta
{
    using namespace App;

    class VerifierStubImpl
    {
    public:
        VerifierStubImpl (ThreadId threadId);
        ~VerifierStubImpl ();

        Timestamp Run (const TransFn* fn);
        void Flush();
        EpochId Verify();

    private:

        SlotId EnsureRecordInStore (const Record& record);
        void EvictRecord (SlotId slotId);
        void RegisterForCallback (const TransFn* fn);
        void HandleUpdate (const Record& preRecord, const Value& postValue);

        bool IsInStore(const BaseKey& baseKey, SlotId* slot);

        void LogTransFn (const TransFn* fn, const SlotId* slots);
        void LogAddMInternal (const BaseKey& key, const MerkleValue* value, SlotId slotId, SlotId parentSlotId);

#ifdef DEBUG
        bool ValidStoreInvariants() const;
#endif

        struct SlotInfo
        {
            BaseKey baseKey;
            SlotId parentSlot;
        };

        MerkleTree merkleTree_;
        SlotInfo slots_[StoreSize];
        SlotId nextFreeSlot_;
    };

}
