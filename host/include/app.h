#pragma once

#include <key.h>
#include <serialize.h>

namespace Zeta
{

namespace App
{
    using Value = Serializable;

    class Key : public Serializable
    {
    public:
        virtual ~Key();
        virtual BaseKey GetBaseKey() const;
    };

    class Record
    {
    public:
        virtual ~Record();
        virtual Key& GetKey() const = 0;
        virtual Value& GetValue() const = 0;
    };

    using Param = Serializable;

    class TransFn
    {
    public:
        TransFn(int arity, bool hasOutput);
        ~TransFn();

        int GetArity() const
        {
            return arity_;
        }

        bool HasOutput() const
        {
            return hasOutput_;
        }

        virtual const Record& GetRecord(int idx) const = 0;

        virtual const Value& GetPostValue(int idx) const = 0;

        virtual bool Touches(int idx) const = 0;

    private:
        const int arity_;
        const bool hasOutput_;
    };

    typedef void (*OutCallback) (const TransFn *fn, const uint8_t* buf, size_t len);
}

}
