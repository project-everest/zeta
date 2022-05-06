#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

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

TEST_CASE("test single function (newcounter)")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, OutputCallback, proxy };

    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();
}

TEST_CASE("test single key init/incr")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, OutputCallback, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();

    // incr counter for key 0 providing pre-image record (0,0)
    Incr incrCounter { 0, Record { 0, 0} };
    verifier.Run(&incrCounter);
    verifier.Flush();
}

TEST_CASE("test single key init/incr with corrupted pre-image")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, OutputCallback, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();

    bool exceptionRaised = false;
    try {
        // incr counter for key 0 providing pre-image record (0,42)
        Incr incrCounter { 0, Record { 0, 42} };
        verifier.Run(&incrCounter);
        verifier.Flush();
    }
    catch (Zeta::VerificationFailureException&)
    {
        exceptionRaised = true;
    }

    REQUIRE(exceptionRaised);
}
