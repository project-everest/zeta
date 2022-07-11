#include <assert.h>
#include <stdexcept>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <app.h>
#include <byteswap.h>

using namespace Zeta;
using namespace Zeta::mcounter;

Key::Key(key_t k) : k_{k} {}

size_t Key::Serialize (uint8_t *buf, size_t size) const
{
    return App_key_app_key_lserializer(k_, buf, 0);
}

size_t Key::SerializationLength() const
{
    return sizeof(key_t);
}

void Key::Serialize4Hash(Hasher &hasher) const
{
    uint8_t buf [sizeof(key_t)];
    Serialize(buf, sizeof(buf));
    hasher.HashPartial(buf, sizeof(buf));
}

Value::Value(value_t v) : v_{v} {}

size_t Value::Serialize (uint8_t *buf, size_t size) const
{
    return App_val_app_val_lserializer(v_, buf, 0);
}

size_t Value::SerializationLength() const
{
    return sizeof(value_t);
}

void Value::Serialize4Hash(Hasher &hasher) const
{
    uint8_t buf [sizeof(value_t)];
    Serialize(buf, sizeof(buf));
    hasher.HashPartial(buf, sizeof(buf));
}

Record::Record(Key::key_t k, Value::value_t v)
    : key_{k}, value_{v}, isNull_{false} {}

Record::Record(Key::key_t k) : key_{k}, value_{}, isNull_{true} {}

const Key &Record::GetKey() const { return key_; }

const Value* Record::GetValue() const
{
    return isNull_? nullptr : &value_;
}

static uint32_t uint64_t_jumper(LowParse_Slice_slice sl, uint32_t pos)
{
    return sizeof(uint64_t);
}

static uint64_t uint64_t_reader(LowParse_Slice_slice sl, uint32_t pos)
{
    uint64_t r;
    memcpy(reinterpret_cast<uint8_t*>(&r), sl.base + pos, sizeof(uint64_t));
    return bswap_64(r);
}

New_Counter::New_Counter
(
     const App_key_app_key* k,
    const Record* r
)
: AppTransFn { 0, 1, false }, k_{*k}
    , r_{*r}
, paramSerializer_ { this }
{

}

const Record& New_Counter::GetRecord(int idx) const
{
    assert (idx < 1);

    if (idx == 0) return r_;

    throw std::invalid_argument("invalid argument");
}

const Value& New_Counter::GetPostValue(int idx) const
{
    assert (idx < 1);

    // TODO: Implement: needed for correct merkle updates

    throw std::runtime_error("not implemented");
}

bool New_Counter::Touches(int idx) const
{
    assert (idx < 1);

    // TODO: Implement correct Touches for better performance
    // by minimizing merkle tree updates

    return true;
}

void New_Counter::SetOutput(ReadLog& log)
{
#ifdef _HAS_OUTPUT_New_Counter
    LowParse_Slice_slice inp { const_cast<uint8_t*>(log.Current()), log.LeftToRead() };
    uint32_t len = Void_void_jumper(inp, 0);
    out_ = Void_void_reader(inp, 0);
    log.DeserializeBuf(len);
#endif
}

New_Counter_ParamSerializer::New_Counter_ParamSerializer(const New_Counter* fn)
  : fn_ { fn }
{

}

size_t New_Counter_ParamSerializer::Serialize(uint8_t *buf, size_t size) const
{
    uint32_t pos = 0;
    uint32_t wrote = 0;

    wrote = App_key_app_key_lserializer (fn_->k_, buf, pos);
    pos += wrote;


    return pos;
}

size_t New_Counter_ParamSerializer::SerializationLength() const
{
    /* Hacky implementation of SerializationLength - fix */
    uint8_t buf [4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    return wrote;
}

void New_Counter_ParamSerializer::Serialize4Hash(Hasher& hasher) const
{
    uint8_t buf[4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    hasher.HashPartial(buf, wrote);
}


Incr_Counter::Incr_Counter
(
     const App_key_app_key* k,
    const Record* r
)
: AppTransFn { 1, 1, true }, k_{*k}
    , r_{*r}
, paramSerializer_ { this }
{

}

const Record& Incr_Counter::GetRecord(int idx) const
{
    assert (idx < 1);

    if (idx == 0) return r_;

    throw std::invalid_argument("invalid argument");
}

const Value& Incr_Counter::GetPostValue(int idx) const
{
    assert (idx < 1);

    // TODO: Implement: needed for correct merkle updates

    throw std::runtime_error("not implemented");
}

bool Incr_Counter::Touches(int idx) const
{
    assert (idx < 1);

    // TODO: Implement correct Touches for better performance
    // by minimizing merkle tree updates

    return true;
}

void Incr_Counter::SetOutput(ReadLog& log)
{
#ifdef _HAS_OUTPUT_Incr_Counter
    LowParse_Slice_slice inp { const_cast<uint8_t*>(log.Current()), static_cast<uint32_t>(log.LeftToRead()) };
    uint32_t len = App_val_app_val_jumper(inp, 0);
    out_ = App_val_app_val_reader(inp, 0);
    log.DeserializeBuf(len);
#endif
}

Incr_Counter_ParamSerializer::Incr_Counter_ParamSerializer(const Incr_Counter* fn)
  : fn_ { fn }
{

}

size_t Incr_Counter_ParamSerializer::Serialize(uint8_t *buf, size_t size) const
{
    uint32_t pos = 0;
    uint32_t wrote = 0;

    wrote = App_key_app_key_lserializer (fn_->k_, buf, pos);
    pos += wrote;


    return pos;
}

size_t Incr_Counter_ParamSerializer::SerializationLength() const
{
    /* Hacky implementation of SerializationLength - fix */
    uint8_t buf [4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    return wrote;
}

void Incr_Counter_ParamSerializer::Serialize4Hash(Hasher& hasher) const
{
    uint8_t buf[4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    hasher.HashPartial(buf, wrote);
}


Get_Counter::Get_Counter
(
     const App_key_app_key* k,
    const Record* r
)
: AppTransFn { 2, 1, true }, k_{*k}
    , r_{*r}
, paramSerializer_ { this }
{

}

const Record& Get_Counter::GetRecord(int idx) const
{
    assert (idx < 1);

    if (idx == 0) return r_;

    throw std::invalid_argument("invalid argument");
}

const Value& Get_Counter::GetPostValue(int idx) const
{
    assert (idx < 1);

    // TODO: Implement: needed for correct merkle updates

    throw std::runtime_error("not implemented");
}

bool Get_Counter::Touches(int idx) const
{
    assert (idx < 1);

    // TODO: Implement correct Touches for better performance
    // by minimizing merkle tree updates

    return true;
}

void Get_Counter::SetOutput(ReadLog& log)
{
#ifdef _HAS_OUTPUT_Get_Counter
    LowParse_Slice_slice inp { const_cast<uint8_t*>(log.Current()), static_cast<uint32_t>(log.LeftToRead()) };
    uint32_t len = uint64_t_jumper(inp, 0);
    out_ = uint64_t_reader(inp, 0);
    log.DeserializeBuf(len);
#endif
}

Get_Counter_ParamSerializer::Get_Counter_ParamSerializer(const Get_Counter* fn)
  : fn_ { fn }
{

}

size_t Get_Counter_ParamSerializer::Serialize(uint8_t *buf, size_t size) const
{
    uint32_t pos = 0;
    uint32_t wrote = 0;

    wrote = App_key_app_key_lserializer (fn_->k_, buf, pos);
    pos += wrote;


    return pos;
}

size_t Get_Counter_ParamSerializer::SerializationLength() const
{
    /* Hacky implementation of SerializationLength - fix */
    uint8_t buf [4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    return wrote;
}

void Get_Counter_ParamSerializer::Serialize4Hash(Hasher& hasher) const
{
    uint8_t buf[4096];
    size_t wrote = Serialize(buf, sizeof(buf));
    hasher.HashPartial(buf, wrote);
}

