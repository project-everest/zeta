#pragma once

#include <app.h>
#include <key.h>
#include <log.h>
#include <merkle_tree.h>

using namespace Zeta::App;

namespace Zeta
{
    class Formats
    {
    public:
        static void LogAddMInternal(const BaseKey& key,
                                    const MerkleValue* value,
                                    SlotId slot, SlotId parentSlot,
                                    WriteLog& log);

        static void LogAddMApp (const Record &record, SlotId slot, SlotId parentSlot, WriteLog& log);

        static void LogEvictM (SlotId s, SlotId ps);

        static void LogRunApp (int arity, const Param& param, const SlotId* slots, WriteLog& log);

        static void GetHashValue (const Value& value, HashValue& hashValBuf);

        static void GetHashValue (const MerkleValue* value, HashValue& hashValBuf);
    };
}
