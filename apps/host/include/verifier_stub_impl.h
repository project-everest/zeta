#pragma once

#include <appcommon.h>
#include <common.h>
#include <log.h>
#include <memory>
#include <merkle_tree.h>
#include <queue>

namespace Zeta
{
    class VerifierStubImpl
    {
    public:
        VerifierStubImpl (ThreadId threadId, OutCallback outCallback);
        ~VerifierStubImpl ();

        Timestamp Run (const AppTransFn* fn);
        void Flush();
        EpochId Verify();

    private:

        SlotId EnsureRecordInStore (const AppRecord& record);
        void EvictSlot (SlotId slotId);
        void RegisterForCallback (const AppTransFn* fn);

        void UpdateMerkleHash(const AppKey& key, const AppValue& newValue, const BaseKey& provingAncestor);
        void UpdateMerkleHash(const BaseKey& key, const MerkleValue* value, const BaseKey& provingAncestor);

        bool IsInStore(const BaseKey& baseKey, SlotId* slot);
        void InitSlots();
        SlotId NewSlotId(const BaseKey& key, SlotId parentSlot);
        void FreeSlot(SlotId s);

#ifdef DEBUG
        bool IsValidSlot(SlotId slotId) const;
#endif

        void EnsureEnoughLogSpace();
        void LogTransFn (const AppTransFn* fn, const SlotId* slots);
        void LogAddMInternal (const BaseKey& key, const MerkleValue* value, SlotId slot, SlotId parentSlot);
        void LogAddMApp (const AppRecord& record, SlotId slot, SlotId parentSlot);
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

        const ThreadId threadId_;
        const OutCallback outCallback_;
        MerkleTree merkleTree_;
        SlotInfo slotInfo_[StoreSize];
        SlotId nextFreeSlot_;
        WriteLog writeLog_;

        std::queue<const AppTransFn*> toCallback_;
        std::unique_ptr<uint8_t> outBuf_;
    };

}
