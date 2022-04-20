#include "merkle_tree.h"
#include <merkle_tree_impl.h>

using namespace Zeta;
using namespace Zeta::internal;

MerkleTree::MerkleTree() : pimpl_{new MerkleTreeImpl()} {}

MerkleTree::~MerkleTree() {}

void MerkleTree::Put(const BaseKey &key, const MerkleValue &value)
{
    pimpl_->Put(key, value);
}

const MerkleValue* MerkleTree::Get(const BaseKey& key) const
{
    return pimpl_->Get(key);
}

MerkleValue* MerkleTree::Get(const BaseKey& key)
{
    return pimpl_->Get(key);
}

UInt256 MerkleTree::GetPath(const BaseKey& ancKey, const BaseKey& leaf) const
{

}
