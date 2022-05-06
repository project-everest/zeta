#include <log.h>
#include <zeta_traits.h>
#include <stdexcept>
#include <cstring>
#include <byteswap.h>

using namespace Zeta;

WriteLog::WriteLog()
    : ubuf_{new uint8_t[LogBufSize]}
    , buf_{ubuf_.get()}
    , bufEnd_{buf_ + LogBufSize}
    , cur_{buf_}
{

}

WriteLog::~WriteLog() {}

void WriteLog::Serialize(const uint8_t* bytes, size_t len)
{
    assert (cur_ <= bufEnd_ && cur_ >= buf_);

    if (cur_ + len > bufEnd_) {
        throw std::runtime_error("log buffer overflow");
    }

    memcpy(cur_, bytes, len);
    cur_ += len;
}

size_t WriteLog::LeftToWrite() const
{
    assert (cur_ <= bufEnd_ && cur_ >= buf_);
    return bufEnd_ - cur_;
}

size_t WriteLog::Written() const
{
    assert (cur_ <= bufEnd_ && cur_ >= buf_);
    return cur_ - buf_;
}

void WriteLog::Clear()
{
    cur_ = buf_;
}

void WriteLog::Serialize(const Serializable& serializable)
{
    assert (cur_ <= bufEnd_ && cur_ >= buf_);

    if (cur_ + serializable.SerializationLength() > bufEnd_) {
        throw std::runtime_error("log buffer overflow");
    }

    auto wrote = serializable.Serialize(cur_, LeftToWrite());
    assert (wrote <= LeftToWrite());
    cur_ += wrote;
}

template <>
void WriteLog::TSerialize<uint16_t>(const uint16_t& v)
{
    uint16_t ve = bswap_16(v);
    Serialize(reinterpret_cast<const uint8_t*>(&ve), sizeof(uint16_t));
}

template <>
void WriteLog::TSerialize<uint32_t>(const uint32_t& v)
{
    uint32_t ve = bswap_32(v);
    Serialize(reinterpret_cast<const uint8_t*>(&ve), sizeof(uint32_t));
}

template <>
void WriteLog::TSerialize<uint64_t>(const uint64_t& v)
{
    uint64_t ve = bswap_64(v);
    Serialize(reinterpret_cast<const uint8_t*>(&ve), sizeof(uint64_t));
}

template <>
void WriteLog::TSerialize<uint8_t>(const uint8_t& v)
{
    Serialize(&v, sizeof(uint8_t));
}

ReadLog::ReadLog(const uint8_t *bytes, size_t len)
    : cur_{bytes}, bufEnd_{cur_ + len} {}

const uint8_t* ReadLog::DeserializeBuf(size_t len)
{
    assert (cur_ <= bufEnd_);

    if (len > LeftToRead()) {
        throw std::runtime_error("trying to read more than left");
    }

    auto p = cur_;
    cur_ += len;

    return p;
}

size_t ReadLog::LeftToRead() const
{
    assert (cur_ <= bufEnd_);

    return bufEnd_ - cur_;
}

template<>
uint64_t ReadLog::DeserializeBigEndian<uint64_t>()
{
    uint64_t v = Deserialize<uint64_t>();
    v = bswap_64(v);
    return v;
}
