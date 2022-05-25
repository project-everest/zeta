    class @name@ : public AppTransFn
    {
    public:
        @constructor@

        const AppParam& GetParam() const override;

        const Record& GetRecord(int idx) const override;

        const Value& GetPostValue(int idx) const override;

        bool Touches(int idx) const override;

        void SetOutput(ReadLog& log) override;

        Value::value_t GetOutput() const
        {
            return out_;
        }

    private:
        Key k_;
        Record r_;
        Value v_;
        Value::value_t out_;
    };
