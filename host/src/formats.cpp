#include "zeta_traits.h"
#include <cstdint>
#include <formats.h>
#include <limits>
#include <stdexcept>

using namespace Zeta;

void Formats::LogAddMInternal(const BaseKey &key, const MerkleValue *value, SlotId s, SlotId ps, WriteLog &log)
{
    const uint8_t entry_kind = 0U;

    log.TSerialize(entry_kind);
    LogRecord(key, value, log);
    LogSlotId(s, log);
    LogSlotId(ps, log);
}

void Formats::LogAddMApp(const Record &record, SlotId s, SlotId ps, WriteLog &log)
{
    const uint8_t entry_kind = 0U;

    log.TSerialize(entry_kind);
    LogRecord(record, log);
    LogSlotId(s, log);
    LogSlotId(ps, log);
}

void Formats::LogEvictM(SlotId s, SlotId ps, WriteLog& log)
{
    const uint8_t entry_kind = 3U;
    log.TSerialize(entry_kind);
    LogSlotId(s, log);
    LogSlotId(ps, log);
}

void Formats::LogRunApp (uint8_t fnId, int arity, const Param& param, const SlotId* slots, WriteLog& log)
{
    const uint8_t entry_kind = 7U;
    log.TSerialize(entry_kind);
    log.TSerialize(fnId);

    size_t length = param.SerializationLength() + sizeof(SlotId) * arity;
    if (length > std::numeric_limits<uint32_t>::max()) {
        throw std::runtime_error("serialization length exceeds 32 bit limit");
    }

    auto length32 = static_cast<uint32_t>(length);
    log.TSerialize(length32);
    log.Serialize(param);
    for (int i = 0 ; i < arity ; ++i) {
        log.TSerialize(slots[i]);
    }
}

void Formats::LogBaseKey (const BaseKey& key, WriteLog& log)
{
    auto pu64 = key.GetPath().Bytes();
    assert (key.IsNormalized());

    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
    log.TSerialize(key.GetDepth());
}

void AddtoHash(const BaseKey& key, Hasher& hasher)
{
    auto pu64 = key.GetPath().Bytes();
    assert (key.IsNormalized());

    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(key.GetDepth());
}

void Formats::LogHashValue (const HashValue& hashValue, WriteLog& log)
{
    auto pu64 = hashValue.Bytes();
    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
    log.TSerialize(*pu64++);
}

void AddtoHash(const HashValue& hashValue, Hasher& hasher)
{
    auto pu64 = hashValue.Bytes();
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
    hasher.HashPartialT(*pu64++);
}

void Formats::LogDescInfo (const DescInfo& descInfo, WriteLog& log)
{
    const uint8_t nullity = (descInfo.isNonNull)? 1U : 0U;
    log.TSerialize(nullity);

    if (descInfo.isNonNull) {
        LogBaseKey(descInfo.key, log);
        LogHashValue(descInfo.hash, log);

        uint8_t bval = descInfo.inBlum? 1U : 0U;
        log.TSerialize(bval);
    }
}



void AddtoHash(const DescInfo& descInfo, Hasher& hasher)
{
    const uint8_t nullity = (descInfo.isNonNull)? 1U : 0U;
    hasher.HashPartialT(nullity);

    if (descInfo.isNonNull) {
        AddtoHash(descInfo.key, hasher);
        AddtoHash(descInfo.hash, hasher);

        uint8_t bval = descInfo.inBlum? 1U : 0U;
        hasher.HashPartialT(bval);
    }
}

void Formats::GetHashValue(const MerkleValue* value, HashValue& hashValBuf)
{
    const uint8_t value_kind = 0U; // MV

    Hasher hasher{};

    hasher.HashPartialT(value_kind);
    AddtoHash(value->descInfo[0], hasher);
    AddtoHash(value->descInfo[1], hasher);
}

void Formats::LogMerkleValue(const MerkleValue* value, WriteLog& log)
{
    assert (value != nullptr);
    LogDescInfo(value->descInfo[0], log);
    LogDescInfo(value->descInfo[1], log);
}

void Formats::LogRecord(const BaseKey& key, const MerkleValue* value, WriteLog& log)
{
    // internal key
    const uint8_t key_type = 0U;

    log.TSerialize(key_type);
    LogBaseKey(key, log);
    LogMerkleValue(value, log);
}

void Formats::LogValue (const Value* value, WriteLog& log)
{
    const uint8_t nullity = (value == nullptr)? 0U : 1U;

    log.TSerialize(nullity);
    log.Serialize(*value);
}

void Formats::LogRecord (const Record& record, WriteLog& log)
{
    const uint8_t key_type = 1U;

    log.TSerialize(key_type);
    log.Serialize(record.GetKey());
    LogValue(record.GetValue(), log);
}

void Formats::GetHashValue(const Value& value, HashValue& hashValBuf)
{
    const uint8_t value_kind = 2U; // DVSome
    Hasher hasher{};

    hasher.HashPartialT(value_kind);
    value.Serialize4Hash(hasher);
    hasher.HashFinal(hashValBuf);
}
