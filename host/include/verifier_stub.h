#pragma once

#include <memory>
#include <common.h>
#include <app.h>

using namespace Zeta::App;

namespace Zeta
{

    class VerifierStubImpl;
    
    class VerifierStub
    {
    public:        
        VerifierStub (ThreadId threadId);
        ~VerifierStub ();
        
        Timestamp Run (const TransFn* fn);
        void Flush();
        EpochId Verify();

    private:
        std::unique_ptr<VerifierStubImpl> pimpl_;
    };

}
