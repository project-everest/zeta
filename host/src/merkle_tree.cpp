#include <merkle_tree.h>
#include <merkle_tree_impl.h>

using namespace Zeta;
using namespace Zeta::internal;

MerkleTree::MerkleTree() : pimpl_{new MerkleTreeImpl()} {}

MerkleTree::~MerkleTree() {}

MerkleValue* MerkleTree::Put(const BaseKey &key)
{
    return pimpl_->Put(key);
}

const MerkleValue* MerkleTree::Get(const BaseKey& key) const
{
    return pimpl_->Get(key);
}

MerkleValue* MerkleTree::Get(const BaseKey& key)
{
    return pimpl_->Get(key);
}
