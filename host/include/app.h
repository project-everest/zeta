#pragma once

#include <key.h>
#include <serialize.h>

namespace Zeta
{
    class AppRecord
    {
    public:
        virtual Serializable& Key() const = 0;
        virtual Serializable& Value() const = 0;

        virtual BaseKey GetBaseKey() const;
    };

    using AppParam = Serializable;
}
