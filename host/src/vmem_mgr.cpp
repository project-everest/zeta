#include "app.h"
#include <assert.h>
#include <common.h>
#include <formats.h>
#include <vmem_mgr.h>
#include <vmem_mgr_impl.h>

using namespace Zeta;

VMemoryManager::VMemoryManager(ThreadId threadId, Log &log)
    : pimpl_ { new VMemoryManagerImpl (threadId, log) }
{

}

void VMemoryManager::BeginOperation() { pimpl_->BeginOperation(); }

SlotId VMemoryManager::Add(const AppRecord *record)
{
    return pimpl_->Add(record);
}

void VMemoryManager::Update(SlotId slotId, const AppRecord *record)
{
    return pimpl_->Update(slotId, record);
}

void VMemoryManager::RunApp (SlotId slotId, const AppParam* param)
{
    return pimpl_->RunApp(slotId, param);
}

void VMemoryManager::RunApp (SlotId slotId0, SlotId slotId1, const AppParam* param)
{
    return pimpl_->RunApp(slotId0, slotId1, param);
}

void VMemoryManager::RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, const AppParam* param)
{
    return pimpl_->RunApp(slotId0, slotId1, slotId2, param);
}

void VMemoryManager::RunApp (SlotId slotId0, SlotId slotId1, SlotId slotId2, SlotId slotId3, const AppParam* param)
{
    return pimpl_->RunApp(slotId0, slotId1, slotId2, slotId3, param);
}

void VMemoryManager::EndOperation()
{
    return pimpl_->EndOperation();
}

VMemoryManagerImpl::VMemoryManagerImpl(ThreadId threadId, Log &log)
    : threadId_ { threadId }
    , log_ { log }
{

}

void VMemoryManagerImpl::BeginOperation()
{
    // do nothing
}

SlotId VMemoryManagerImpl::Add(const AppRecord* record)
{
    auto appBaseKey = record->GetBaseKey();
    assert (appBaseKey.GetDepth() == BaseKey::LeafDepth);

    auto curKey = BaseKey::Root;

    while (curKey.GetDepth() < appBaseKey.GetDepth()) {

        // invariant: curKey is an ancestor of baseKey that exists in the merkle tree
        assert (curKey.IsAncestor(appBaseKey));

        auto curValue = merkleTree_.Get(curKey);
        assert (curValue != nullptr);

        // if curKey is not root, then it is not in verifier store; add it
        if (!curKey.IsRoot()) {
            AddInternal(curKey, curValue);
        }

        auto dir = DescDirTr::ToByte(curKey.GetDescDir(appBaseKey));
        assert (dir < 2);

        auto nextKey = curValue->descInfo[dir].key;

        if (!nextKey.IsAncestor(appBaseKey)) {

            auto newKey = BaseKey::GetLeastCommonAncestor(appBaseKey, nextKey);
            assert (newKey.IsDescendant(curKey) && newKey.GetDepth() > curKey.GetDepth());
            assert (newKey.IsAncestor(nextKey) && newKey.GetDepth() < nextKey.GetDepth());
            assert (newKey.IsAncestor(appBaseKey) && newKey.GetDepth() < BaseKey::LeafDepth);

            auto newVal = merkleTree_.Put(newKey);
            auto dir2 = DescDirTr::ToByte(newKey.GetDescDir(appBaseKey));
            auto odir2 = 1 - dir2;

            newVal->descInfo[dir2].key = appBaseKey;
            newVal->descInfo[odir2].key = newKey;
            newVal->descInfo[odir2].inBlum = curValue->descInfo[dir].inBlum;

            curValue->descInfo[dir].inBlum = false;
            curValue->descInfo[dir].key = newKey;

            curKey = newKey;
        }
        else {
            curKey = nextKey;
        }
    }

    auto parentSlot = nextSlot_;
    auto slot = nextSlot_++;
    Formats::LogAddMApp(record, slot, parentSlot, log_);

    return slot;
}

void VMemoryManagerImpl::RunApp(SlotId slotId, const AppParam* record)
{

}

void VMemoryManagerImpl::AddInternal(const BaseKey& key, const MerkleValue* value)
{
    assert (value != nullptr);

    auto parentSlot = nextSlot_;
    auto slot = nextSlot_++;

    Formats::LogAddMInternal(key, value, slot, parentSlot, log_);
}
