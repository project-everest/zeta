#pragma once

#include <common.h>
#include <app.h>

namespace Zeta
{
    using namespace App;

    class VerifierStubImpl
    {
    public:
        VerifierStubImpl (ThreadId threadId);
        ~VerifierStubImpl ();

        Timestamp Run (const TransFn* fn);
        void Flush();
        EpochId Verify();
    };

}
