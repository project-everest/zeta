#pragma once

#include <key.h>

namespace Zeta
{
    class AppRecord
    {
    public:
        virtual BaseKey GetBaseKey() const = 0;

        virtual size_t SerializeKey (uint8_t* buf, size_t size) const = 0;
        virtual size_t SerializeValue (uint8_t* buf, size_t size) const = 0;
    };
}
