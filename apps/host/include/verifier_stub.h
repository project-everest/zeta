#pragma once

#include <memory>
#include <common.h>
#include <appcommon.h>

namespace Zeta
{

    class VerifierStubImpl;

    typedef void (*VerifyLogFn) (ThreadId threadId,
                                 const uint8_t *inp,
                                 size_t inpLen,
                                 uint8_t *out,
                                 size_t outBufSize,
                                 size_t *outLen);

    struct VerifierProxy
    {
        VerifyLogFn VerifyLog;
    };
    
    class VerifierStub
    {
    public:        
        VerifierStub (ThreadId threadId, OutCallback outCallback, VerifierProxy verifierProxy);
        ~VerifierStub ();
        
        Timestamp Run (const AppTransFn* fn);
        void Flush();
        EpochId Verify();

    private:
        std::unique_ptr<VerifierStubImpl> pimpl_;
    };

}
