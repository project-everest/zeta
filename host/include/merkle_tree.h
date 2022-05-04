#pragma once
#include <zeta_config.h>
#include <zeta_traits.h>
#include <common.h>
#include <crypt_hash.h>
#include <key.h>
#include <memory>

namespace Zeta
{
    struct DescInfo
    {
        BaseKey key;
        HashValue hash;
        bool inBlum;
        bool isNonNull;
    };

    struct MerkleValue
    {
        DescInfo descInfo[2];

        MerkleValue() {
            descInfo[0].isNonNull = false;
            descInfo[1].isNonNull = false;
        }
    };


    // Forward decl of MerkleTree impl for pimpl
    class MerkleTreeImpl;

    class MerkleTree
    {
    public:
        MerkleTree();
        ~MerkleTree();

        MerkleValue* Put (const BaseKey& key);
        const MerkleValue* Get(const BaseKey& key) const;
        MerkleValue* Get (const BaseKey& key);

    private:
        std::unique_ptr<MerkleTreeImpl> pimpl_;
    };
} // namespace Zeta
