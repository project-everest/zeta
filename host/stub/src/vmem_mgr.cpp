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

void VMemoryManager::EndOperation()
{
    return pimpl_->EndOperation();
}
