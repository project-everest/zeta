#include <app.h>
#include <trace.h>
#include <verifier_proxy.h>
#include <verifier_stub.h>

using namespace Zeta;
using namespace Zeta::mcounter;

void OutputCallback (const AppTransFn *fn, const uint8_t *buf, size_t len)
{

}

static VerifierProxy GetVerifierProxy()
{
    verifier_init();

    VerifierProxy proxy { &verifier_verify_log };

    return proxy;
}

int main(int argc, char *argv[])
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, OutputCallback, proxy };
    LOG_LEVEL_DEBUG;

    Record r { 0 };
    New newCounter { 0, r };
    verifier.Run(&newCounter);
    verifier.Flush();

    Incr incrCounter { 0, Record { 0, 0} };
    verifier.Run(&incrCounter);
    verifier.Flush();

    return 0;
}
