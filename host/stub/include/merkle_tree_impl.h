#pragma once

#include <assert.h>
#include <merkle_tree.h>
#include <unordered_map>

namespace Zeta
{

namespace internal
{


    struct BaseKeyHash
    {
        std::size_t operator() (const BaseKey& key) {
            assert (key.IsNormalized());
            auto bytes = key.GetPath().Bytes();
            return bytes[0] ^ bytes[1] ^ bytes[2] ^ bytes[3] ^ std::hash<uint16_t>{}(key.GetDepth());
        }
    };

    struct BaseKeyEqual
    {
        bool operator() (const BaseKey& key1, const BaseKey& key2) {
            assert(key1.IsNormalized() && key2.IsNormalized());
            return key1.GetPath() == key2.GetPath() &&
                key1.GetDepth() == key2.GetDepth();
        }
    };

    class MerkleTreeImpl
    {
    public:
        MerkleTreeImpl();
        ~MerkleTreeImpl();

        void Put(const BaseKey& key, const MerkleValue& value);
        const MerkleTree* Get(const BaseKey& key) const;
        MerkleValue* Get (const BaseKey& key);

    private:
        std::unordered_map<BaseKey, MerkleValue, BaseKeyHash, BaseKeyEqual> mt_;
    };


}

}
