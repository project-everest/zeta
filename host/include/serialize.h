#pragma once

#include <cstdint>

namespace Zeta
{
    class Serializable
    {
    public:
        virtual size_t Serialize (uint8_t *buf, size_t size) const = 0;
        virtual size_t SerializationLength() const = 0;
    };
}
