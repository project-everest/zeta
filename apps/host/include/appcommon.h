#pragma once

#include <key.h>
#include <serialize.h>
#include <stdint.h>

namespace Zeta
{

namespace App
{
    using Value = Serializable;

    class Key : public Serializable
    {
    public:
        virtual ~Key() = default;
        virtual BaseKey GetBaseKey() const;
    };

    class Record
    {
    public:
        virtual ~Record() = default;
        virtual const Key& GetKey() const = 0;
        virtual const Value* GetValue() const = 0;
    };

    using Param = Serializable;

    class TransFn
    {
    public:
        TransFn(uint8_t id, int arity, bool hasOutput);
        virtual ~TransFn() = default;

        uint8_t GetId() const
        {
            return id_;
        }

        int GetArity() const
        {
            return arity_;
        }

        bool HasOutput() const
        {
            return hasOutput_;
        }

        virtual const Param& GetParam() const = 0;

        virtual const Record& GetRecord(int idx) const = 0;

        virtual const Value& GetPostValue(int idx) const = 0;

        virtual bool Touches(int idx) const = 0;

    private:
        const uint8_t id_;
        const int arity_;
        const bool hasOutput_;
    };

    typedef void (*OutCallback) (const TransFn *fn, const uint8_t* buf, size_t len);
}

}
