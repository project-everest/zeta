#pragma once
#include <zeta_config.h>
#include <zeta_traits.h>
#include <common.h>
#include <crypt_hash.h>
#include <key.h>
#include <memory>

namespace Zeta
{

namespace internal
{

    struct DescInfo
    {
        BaseKey key;
        HashValue hash;
        bool inBlum;
    };

    struct MerkleValue
    {
        DescInfo descInfo[2];
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


} // namespace internal

} // namespace Zeta
