#include <log.h>
#include <zeta_traits.h>
#include <stdexcept>
#include <cstring>

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
