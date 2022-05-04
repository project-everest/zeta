#include <assert.h>
#include <merkle_tree.h>
#include <merkle_tree_impl.h>

using namespace Zeta;

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

MerkleTreeImpl::MerkleTreeImpl() : mt_{} {}

MerkleTreeImpl::~MerkleTreeImpl() {}

MerkleValue* MerkleTreeImpl::Put(const BaseKey& key)
{
    assert (Get(key) == nullptr);
    auto& mv = mt_[key];
    return &mv;
}

MerkleValue* MerkleTreeImpl::Get(const BaseKey& key)
{
    auto it = mt_.find(key);

    if (it == mt_.end()) {
        return nullptr;
    }
    else {
        return &(it->second);
    }
}

const MerkleValue* MerkleTreeImpl::Get(const BaseKey& key) const
{
    auto it = mt_.find(key);

    if (it == mt_.end()) {
        return nullptr;
    }
    else {
        return &(it->second);
    }
}
