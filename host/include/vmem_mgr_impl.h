#pragma once

#include <app.h>
#include <common.h>
#include <key.h>
#include <log.h>
#include <merkle_tree.h>

namespace Zeta
{
    class VMemoryManagerImpl
    {
    public:
        VMemoryManagerImpl(ThreadId threadId);

        void BeginOperation();

        SlotId Add (const AppRecord* record);
        void Update (SlotId slotId, const AppRecord* record);
        void RunApp (SlotId slotId, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, SlotId slotId3, const AppParam* param);

        void EndOperation();

    private:
        SlotId GetFreeSlot();
        SlotId AddInternal(const BaseKey& key, const MerkleValue* value, SlotId parentSlot);

        const ThreadId threadId_;
        MerkleTree merkleTree_;
        Log log_;
    };
}
