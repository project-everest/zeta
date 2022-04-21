#pragma once

#include <app.h>
#include <key.h>
#include <merkle_tree.h>

namespace Zeta
{
    class Formats
    {
        static void LogAddMInternal(const BaseKey& key, const MerkleValue* value, SlotId slot, SlotId parentSlot);
    };
}
