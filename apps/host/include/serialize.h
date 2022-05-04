#pragma once

#include <stddef.h>
#include <stdint.h>
#include <zeta_traits.h>

namespace Zeta
{
    class Serializable
    {
    public:
        virtual size_t Serialize (uint8_t *buf, size_t size) const = 0;
        virtual size_t SerializationLength() const = 0;
        virtual void Serialize4Hash(Hasher& hasher) const = 0;
    };
}
