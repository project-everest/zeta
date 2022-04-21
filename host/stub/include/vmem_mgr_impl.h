#pragma once

#include <common.h>
#include <record.h>

namespace Zeta
{


    class VMemoryManagerImpl
    {
    public:
        VMemoryManagerImpl(ThreadId threadId);

        void BeginOperation();

        SlotId Add (const AppRecord* record);
        void Update (SlotId slotId, const AppRecord* record);

        void EndOperation();

    private:

        const ThreadId threadId_;

    };

}
