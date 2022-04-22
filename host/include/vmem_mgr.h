#pragma once

#include <memory>
#include <common.h>
#include <log.h>
#include <app.h>

namespace Zeta
{
    class VMemoryManagerImpl;

    class VMemoryManager
    {
    public:
        VMemoryManager (ThreadId threadId, Log& log);
        ~VMemoryManager() = default;

        void BeginOperation();

        SlotId Add (const AppRecord* record);

        void Update (SlotId slotId, const AppRecord* record);

        void RunApp (SlotId slotId, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, const AppParam* param);
        void RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, SlotId slotId3, const AppParam* param);

        void EndOperation();

    private:
        std::unique_ptr<VMemoryManagerImpl> pimpl_;
    };
}
