#include <assert.h>
#include <common.h>
#include <formats.h>
#include <vmem_mgr.h>
#include <vmem_mgr_impl.h>

using namespace Zeta;

VMemoryManager::VMemoryManager(ThreadId threadId)
    : pimpl_ { new VMemoryManagerImpl (threadId) }
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

VMemoryManagerImpl::VMemoryManagerImpl(ThreadId threadId)
    : threadId_ { threadId }
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
    auto curSlot = InvalidSlotId;

    while (curKey.GetDepth() < appBaseKey.GetDepth()) {

        // invariant: curKey is the ancestor of baseKey
        assert (curKey.IsAncestor(appBaseKey));

        auto curValue = merkleTree_.Get(curKey);
        assert (curValue != nullptr);

        if (!curKey.IsRoot()) {
            curSlot = AddInternal(curKey, curValue, curSlot);
        }
        else {
            curSlot = 0;
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
    }

    return 0;
}

SlotId VMemoryManagerImpl::AddInternal(const BaseKey& key, const MerkleValue* value, SlotId parentSlot)
{
    return 0;
}
