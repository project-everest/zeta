#include <cstdint>
#include <formats.h>

using namespace Zeta;

void Formats::LogAddMInternal(const BaseKey &key, const MerkleValue *value, SlotId s, SlotId ps, WriteLog &log)
{
    const uint8_t entry_kind = 0U;

    log.TSerialize<uint8_t>(entry_kind);
    LogRecord(key, value, log);
    LogSlotId(s, log);
    LogSlotId(ps, log);
}

void Formats::LogAddMApp(const Record &record, SlotId s, SlotId ps, WriteLog &log)
{
    const uint8_t entry_kind = 0U;

    log.TSerialize<uint8_t>(entry_kind);
    LogRecord(record, log);
    LogSlotId(s, log);
    LogSlotId(ps, log);
}

void Formats::LogEvictM(SlotId s, SlotId ps, WriteLog& log)
{
    const uint8_t entry_kind = 3U;
    log.TSerialize<uint8_t>(entry_kind);
}
