#pragma once

#include <memory>
#include <common.h>
#include <appcommon.h>

namespace Zeta
{
    class VerifierStubImpl;

    typedef int (*VerifyLogFn) (ThreadId threadId,
                                uint8_t *inp,
                                size_t inpLen,
                                uint8_t *out,
                                size_t outBufSize,
                                size_t *outLen);

    struct VerifierProxy
    {
        VerifyLogFn VerifyLog;
    };

    struct VerificationFailureException {};
    struct VerifierParsingFailure {};
    struct VerifierAppFailure {};
    struct VerifierEntryFailure{};

    class VerifierStub
    {
    public:
        VerifierStub (ThreadId threadId, VerifierProxy verifierProxy);
        ~VerifierStub ();

        Timestamp Run (AppTransFn* fn);
        void Flush();
        EpochId Verify();

    private:
        std::unique_ptr<VerifierStubImpl> pimpl_;
    };
}
