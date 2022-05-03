#pragma once

#include <cstdint>

namespace Zeta
{

    class WriteLog
    {
    public:
        WriteLog();
        ~WriteLog();

        void Serialize(const uint8_t* bytes, size_t len);

        template<typename T>
        void TSerialize(const T& v);

        size_t LeftToWrite() const;

    private:
        uint8_t *buf_;
        uint8_t *cur_;
        size_t bufSize_;
    };

    class ReadLog
    {
    public:
        ReadLog(const uint8_t* bytes, size_t len);

        template<typename T>
        T Deserialize();

        const uint8_t* DeserializeBuf(size_t len);

        size_t LeftToRead() const;
    };
}
