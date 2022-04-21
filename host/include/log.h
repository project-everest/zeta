#pragma once

#include <cstdint>

namespace Zeta
{

    class Log
    {
    public:
        Log();
        ~Log();

        void Serialize(const uint8_t* bytes, size_t len);
        void TSerialize<T>(const T& v);

    private:
        uint8_t *buf_;
        uint8_t *cur_;
        size_t bufSize_;
    };

}
