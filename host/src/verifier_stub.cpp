#include <verifier_stub.h>
#include <verifier_stub_impl.h>

namespace Zeta
{

    VerifierStub::VerifierStub (ThreadId threadId)
        : pimpl_ { new VerifierStubImpl (threadId) }
    {

    }


}
