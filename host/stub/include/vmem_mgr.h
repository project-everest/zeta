#pragma once

#include <memory>
#include <common.h>
#include <record.h>


namespace Zeta
{
    class VMemoryManagerImpl;

    class VMemoryManager
    {
    public:
        VMemoryManager (ThreadId threadId);
        ~VMemoryManager() = default;

        void BeginOperation();

        SlotId Add (const AppRecord* record);

        void Update (SlotId slotId, const AppRecord* record);

        void EndOperation();

    private:
        std::unique_ptr<VMemoryManagerImpl> pimpl_;
    };
}
