#pragma once

#include <appcommon.h>
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
                                    WriteLog& log);

        static void LogAddMApp (const AppRecord &record, SlotId slot, SlotId parentSlot, WriteLog& log);

        static void LogEvictM (SlotId s, SlotId ps, WriteLog& log);

        static void LogRunApp (uint8_t fnId, int arity, const AppParam& param, const SlotId* slots, WriteLog& log);

        static void GetHashValue (const AppValue& value, HashValue& hashValBuf);

        static void GetHashValue (const MerkleValue* value, HashValue& hashValBuf);

    private:
        static void LogRecord (const BaseKey& key, const MerkleValue* value, WriteLog& log);
        static void LogRecord (const AppRecord& record, WriteLog& log);
        static void LogSlotId (SlotId slotId, WriteLog& log);
        static void LogBaseKey (const BaseKey& key, WriteLog& log);
        static void LogMerkleValue (const MerkleValue* value, WriteLog& log);
        static void LogDescInfo (const DescInfo& descInfo, WriteLog& log);
        static void LogHashValue (const HashValue& hashValue, WriteLog& log);
        static void LogValue (const AppValue* value, WriteLog& log);
    };
}
