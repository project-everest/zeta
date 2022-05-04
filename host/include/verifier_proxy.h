#pragma once

#include <stddef.h>
#include <common.h>

namespace Zeta
{
    enum class VerifierReturnCode
    {
        ParsingFailure,
        AppFailure,
        EntryFailure,
        Success
    };

    class VerifierProxy
    {
    public:
        static void Init();
        static VerifierReturnCode VerifyLog(ThreadId threadId,
                                            const uint8_t *inp,
                                            size_t inpLen,
                                            uint8_t *out,
                                            size_t outBufSize,
                                            size_t *outLen);
    };

}
