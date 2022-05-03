#pragma once

#include <app.h>
#include <common.h>
#include <log.h>
#include <memory>
#include <merkle_tree.h>
#include <queue>

namespace Zeta
{
    using namespace App;

    class VerifierStubImpl
    {
    public:
        VerifierStubImpl (ThreadId threadId, OutCallback outCallback);
        ~VerifierStubImpl ();

        Timestamp Run (const TransFn* fn);
        void Flush();
        EpochId Verify();

    private:

        SlotId EnsureRecordInStore (const Record& record);
        void EvictSlot (SlotId slotId);
        void RegisterForCallback (const TransFn* fn);

        void GetHashValue (const Value& value, HashValue& hashValBuf);
        void GetHashValue (const MerkleValue* value, HashValue& hashValBuf);

        void UpdateMerkleHash(const Key& key, const Value& newValue, const BaseKey& provingAncestor);
        void UpdateMerkleHash(const BaseKey& key, const MerkleValue* value, const BaseKey& provingAncestor);

        bool IsInStore(const BaseKey& baseKey, SlotId* slot);
        void InitSlots();
        SlotId NewSlotId(const BaseKey& key, SlotId parentSlot);
        void FreeSlot(SlotId s);

#ifdef DEBUG
        bool IsValidSlot(SlotId slotId) const;
#endif

        void LogTransFn (const TransFn* fn, const SlotId* slots);
        void LogAddMInternal (const BaseKey& key, const MerkleValue* value, SlotId slot, SlotId parentSlot);
        void LogAddMApp (const Record& record, SlotId slot, SlotId parentSlot);
        void LogEvictM (SlotId s, SlotId ps);
        void FlushImpl();

#ifdef DEBUG
        bool ValidStoreInvariants() const;
#endif

        struct SlotInfo
        {
            BaseKey baseKey;
            SlotId parentSlot;
            bool touched;
        };

        const OutCallback outCallback_;
        MerkleTree merkleTree_;
        SlotInfo slotInfo_[StoreSize];
        SlotId nextFreeSlot_;
        WriteLog writeLog_;

        std::queue<const TransFn*> toCallback_;
        std::unique_ptr<uint8_t> outBuf_;
    };

}
