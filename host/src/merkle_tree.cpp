#include "merkle_tree.h"
#include "key.h"
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
    UInt256 path{};

    auto pAncKey = &ancKey;

    assert (pAncKey->GetDepth() != BaseKey::LeafDepth);

    while (pAncKey->IsAncestor(leaf) && pAncKey->GetDepth() < BaseKey::LeafDepth)
    {
        // Safe to cast to 8 bits
        assert(pAncKey->GetDepth() < 256);
        path.SetBit(static_cast<uint8_t>(ancKey.GetDepth()));

        auto dir = ancKey.GetDescDir(leaf);
        auto idir = static_cast<uint8_t>(dir);
        assert (idir < 2);

        auto mv = Get(ancKey);
        assert (mv != nullptr);

        pAncKey = &mv->descInfo_[idir].key;
    }

    return path;
}
