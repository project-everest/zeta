#pragma once

#include <memory>
#include <stdint.h>
#include <serialize.h>

namespace Zeta
{

    class WriteLog
    {
    public:
        WriteLog();
        ~WriteLog();

        void Serialize(const uint8_t* bytes, size_t len);
        void Serialize(const Serializable& serializable);


        template<typename T>
        void TSerialize(const T& v) {
            Serialize(reinterpret_cast<const uint8_t*>(&v), sizeof(T));
        }

        size_t LeftToWrite() const;

        size_t Written() const;

        const uint8_t* Bytes() const
        {
            return buf_;
        }

        void Clear();

    private:
        std::unique_ptr<uint8_t[]> ubuf_;

        uint8_t *const buf_;
        uint8_t *const bufEnd_;
        uint8_t *cur_;
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
