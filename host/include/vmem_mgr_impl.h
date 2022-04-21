#pragma once

#include <app.h>
#include <key.h>
#include <common.h>
#include <merkle_tree.h>

using Zeta::internal::MerkleTree;

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

        const ThreadId threadId_;
        MerkleTree merkleTree_;
    };
}
