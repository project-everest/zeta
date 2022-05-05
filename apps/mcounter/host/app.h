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

    class New : public AppTransFn
    {
    public:
        New (const Key::key_t k, const Record& r);

        const AppParam& GetParam() const override;

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

    private:
        Key k_;
        Record r_;
    };

    class Incr : public AppTransFn
    {
    public:
        Incr (const Key::key_t k, const Record& r);

        const AppParam& GetParam() const override;

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

    private:
        Key k_;
        Record r_;
        Value v_;
    };

    class Get : public AppTransFn
    {
    public:
        Get (const Key::key_t k, const Record& r);

        const AppParam& GetParam() const override;

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

    private:
        Key k_;
        Record r_;
    };

}
}
