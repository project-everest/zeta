#pragma once

#include <memory>
#include <common.h>
#include <appcommon.h>

namespace Zeta
{

    class VerifierStubImpl;
    
    class VerifierStub
    {
    public:        
        VerifierStub (ThreadId threadId, OutCallback outCallback);
        ~VerifierStub ();
        
        Timestamp Run (const AppTransFn* fn);
        void Flush();
        EpochId Verify();

    private:
        std::unique_ptr<VerifierStubImpl> pimpl_;
    };

}
