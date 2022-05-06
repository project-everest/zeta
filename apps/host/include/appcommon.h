#pragma once

#include <key.h>
#include <log.h>
#include <serialize.h>
#include <stdint.h>

namespace Zeta
{
    using AppValue = Serializable;

    class AppKey : public Serializable
    {
    public:
        virtual ~AppKey() = default;
        virtual BaseKey GetBaseKey() const;
    };

    class AppRecord
    {
    public:
        virtual ~AppRecord() = default;
        virtual const AppKey& GetKey() const = 0;
        virtual const AppValue* GetValue() const = 0;
    };

    using AppParam = Serializable;

    class AppTransFn
    {
    public:
        AppTransFn(uint8_t id, int arity, bool hasOutput);
        virtual ~AppTransFn() = default;

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

        virtual const AppParam& GetParam() const = 0;

        virtual const AppRecord& GetRecord(int idx) const = 0;

        virtual const AppValue& GetPostValue(int idx) const = 0;

        virtual bool Touches(int idx) const = 0;

        virtual void SetOutput(ReadLog& log) { /* do nothing */ }

    private:
        const uint8_t id_;
        const int arity_;
        const bool hasOutput_;
    };
}
