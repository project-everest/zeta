#pragma once

#include <app.h>
#include <key.h>
#include <log.h>
#include <merkle_tree.h>

namespace Zeta
{
    class Formats
    {
    public:
        static void LogAddMInternal(const BaseKey& key,
                                    const MerkleValue* value,
                                    SlotId slot, SlotId parentSlot,
                                    Log& log);

        static void LogAddMApp (const AppRecord* record, SlotId slot, SlotId parentSlot, Log& log);
    };
}
