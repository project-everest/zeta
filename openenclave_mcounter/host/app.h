#include <appcommon.h>

extern "C" {
#include <App_key.h>
#include <App_val.h>
}

namespace Zeta
{

namespace mcounter
{

    class Key : public AppKey
    {
    public:
        using key_t = App_key_app_key;

        Key (key_t k);
        size_t Serialize (uint8_t *buf, size_t size) const override;
        size_t SerializationLength() const override;
        void Serialize4Hash(Hasher& hasher) const override;

    private:
        key_t k_;
    };

    class Value : public Serializable
    {
    public:
        using value_t = App_val_app_val;

        Value () = default;
        Value (value_t v);
        size_t Serialize (uint8_t *buf, size_t size) const override;
        size_t SerializationLength() const override;
        void Serialize4Hash(Hasher& hasher) const override;

        value_t Get() const { return v_; }

    private:
        value_t v_;
    };

    class Record : public AppRecord
    {
    public:
        Record (Key::key_t k, Value::value_t v);
        Record (Key::key_t k);

        const Key& GetKey() const override;
        const Value* GetValue() const override;

    private:
        Key key_;
        Value value_;
        bool isNull_;
    };

    class New_Counter;

    class New_Counter_ParamSerializer : public AppParam
    {
    public:
        New_Counter_ParamSerializer(const New_Counter* fn);
        virtual size_t Serialize (uint8_t *buf, size_t size) const override;
        virtual size_t SerializationLength() const override;
        virtual void Serialize4Hash(Hasher& hasher) const override;

    private:
        const New_Counter* fn_;
    };

#define _HAS_NO_OUTPUT_New_Counter

    class New_Counter : public AppTransFn
    {
    public:
        New_Counter (
            const App_key_app_key* k,
            const Record* r
        );

#ifdef _HAS_OUTPUT_New_Counter
        using out_t = Void_void;
#endif

        const AppParam& GetParam() const override
        {
            return paramSerializer_;
        }

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

        void SetOutput(ReadLog& log) override;

#ifdef _HAS_OUTPUT_New_Counter
        const out_t *GetOutput() const
        {
            return &out_;
        }
#endif

    private:

        friend class New_Counter_ParamSerializer;

        App_key_app_key k_;
        Record r_;

        New_Counter_ParamSerializer paramSerializer_;

#ifdef _HAS_OUTPUT_New_Counter
        out_t out_;
#endif
    };


    class Incr_Counter;

    class Incr_Counter_ParamSerializer : public AppParam
    {
    public:
        Incr_Counter_ParamSerializer(const Incr_Counter* fn);
        virtual size_t Serialize (uint8_t *buf, size_t size) const override;
        virtual size_t SerializationLength() const override;
        virtual void Serialize4Hash(Hasher& hasher) const override;

    private:
        const Incr_Counter* fn_;
    };

#define _HAS_OUTPUT_Incr_Counter

    class Incr_Counter : public AppTransFn
    {
    public:
        Incr_Counter (
            const App_key_app_key* k,
            const Record* r
        );

#ifdef _HAS_OUTPUT_Incr_Counter
        using out_t = App_val_app_val;
#endif

        const AppParam& GetParam() const override
        {
            return paramSerializer_;
        }

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

        void SetOutput(ReadLog& log) override;

#ifdef _HAS_OUTPUT_Incr_Counter
        const out_t *GetOutput() const
        {
            return &out_;
        }
#endif

    private:

        friend class Incr_Counter_ParamSerializer;

        App_key_app_key k_;
        Record r_;

        Incr_Counter_ParamSerializer paramSerializer_;

#ifdef _HAS_OUTPUT_Incr_Counter
        out_t out_;
#endif
    };


    class Get_Counter;

    class Get_Counter_ParamSerializer : public AppParam
    {
    public:
        Get_Counter_ParamSerializer(const Get_Counter* fn);
        virtual size_t Serialize (uint8_t *buf, size_t size) const override;
        virtual size_t SerializationLength() const override;
        virtual void Serialize4Hash(Hasher& hasher) const override;

    private:
        const Get_Counter* fn_;
    };

#define _HAS_OUTPUT_Get_Counter

    class Get_Counter : public AppTransFn
    {
    public:
        Get_Counter (
            const App_key_app_key* k,
            const Record* r
        );

#ifdef _HAS_OUTPUT_Get_Counter
        using out_t = uint64_t;
#endif

        const AppParam& GetParam() const override
        {
            return paramSerializer_;
        }

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

        void SetOutput(ReadLog& log) override;

#ifdef _HAS_OUTPUT_Get_Counter
        const out_t *GetOutput() const
        {
            return &out_;
        }
#endif

    private:

        friend class Get_Counter_ParamSerializer;

        App_key_app_key k_;
        Record r_;

        Get_Counter_ParamSerializer paramSerializer_;

#ifdef _HAS_OUTPUT_Get_Counter
        out_t out_;
#endif
    };


}
}
