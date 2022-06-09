#include <assert.h>
#include <stdexcept>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <app.h>

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

New::New(const Key::key_t k, const Record &r)
    : AppTransFn { 0, 1, false }
    , k_ { k }
    , r_ { r }
{

}

const AppParam& New::GetParam() const
{
    return k_;
}

const Record& New::GetRecord(int idx) const
{
    assert (idx == 0);
    return r_;
}

static Value zero { 0 };

const Value& New::GetPostValue(int idx) const
{
    assert (idx == 0);
    return zero;
}

bool New::Touches(int idx) const
{
    assert (idx == 0);
    return true;
}

Incr::Incr(const Key::key_t k, const Record &r)
    : AppTransFn { 1, 1, true }
    , k_ { k }
    , r_ { r }
    , v_ { 1 + r_.GetValue()->Get() }
    , out_ { 0 }
{

}

const AppParam& Incr::GetParam() const
{
    return k_;
}

const Record& Incr::GetRecord(int idx) const
{
    assert (idx == 0);
    return r_;
}

const Value& Incr::GetPostValue(int idx) const
{
    assert (idx == 0);
    return v_;
}

bool Incr::Touches(int idx) const
{
    assert (idx == 0);
    return true;
}


void Incr::SetOutput(ReadLog& log)
{
    out_ = log.DeserializeBigEndian<Value::value_t>();
}

Get::Get(const Key::key_t k, const Record &r)
    : AppTransFn { 2, 1, true }
    , k_ { k }
    , r_ { r }
    , out_ { 0 }
{

}

const AppParam& Get::GetParam() const
{
    return k_;
}

const Record& Get::GetRecord(int idx) const
{
    assert (idx == 0);
    return r_;
}

const Value& Get::GetPostValue(int idx) const
{
    throw std::logic_error("post value accessed for get");
}

bool Get::Touches(int idx) const
{
    assert (idx == 0);
    return false;
}

void Get::SetOutput(ReadLog& log)
{
    out_ = log.DeserializeBigEndian<Value::value_t>();
}
