#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <app.h>
#include <trace.h>
#include <verifier_proxy.h>
#include <verifier_stub.h>

using namespace Zeta;
using namespace Zeta::mcounter;

static VerifierProxy GetVerifierProxy()
{
    verifier_init();
    VerifierProxy proxy { &verifier_verify_log };
    return proxy;
}

TEST_CASE("test single function (newcounter)")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();
}

TEST_CASE("test single key init/incr")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();

    // incr counter for key 0 providing pre-image record (0,0)
    Incr incrCounter { 0, Record { 0, 0} };
    verifier.Run(&incrCounter);
    verifier.Flush();

    // the output of the operation is the prev value which is 0
    REQUIRE(incrCounter.GetOutput() == 0);
}

TEST_CASE("test single key init/incr with batching")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);

    // incr counter for key 0 providing pre-image record (0,0)
    Incr incrCounter { 0, Record { 0, 0} };
    verifier.Run(&incrCounter);

    // verify both operations in a batch
    verifier.Flush();

    // the output of the operation is the prev value which is 0
    REQUIRE(incrCounter.GetOutput() == 0);
}

TEST_CASE("test single key init/incr with corrupted pre-image")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();

    bool exceptionRaised = false;
    try {
        // incr counter for key 0 providing corrupted value of record (0,42)
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

TEST_CASE("test single key output")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    // initialize a counter for key 0
    New newCounter { 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();

    // incr counter for key 0 providing pre-image record (0,0)
    Incr incrCounter { 0, Record { 0, 0} };
    verifier.Run(&incrCounter);
    verifier.Flush();

    // read the counter for key 0
    Get getCounter { 0, Record { 0, 1 } };
    verifier.Run(&getCounter);
    verifier.Flush();

    // the read value should be 1
    REQUIRE(getCounter.GetOutput() == 1);
}

TEST_CASE("test ops on a sequential key range")
{
    static const uint64_t KeyCount = 2;
    LOG_LEVEL_DEBUG;
    auto proxy = GetVerifierProxy();

    VerifierStub verifier { 0, proxy };

    // initialize a bunch of counters
    for (uint64_t i = 0 ; i < KeyCount ; ++i) {
        New newCounter { i, Record { i } };
        verifier.Run(&newCounter);
    }
    verifier.Flush();

    // incr all counters
    for (uint64_t i = 0 ; i < KeyCount ; ++i) {
        Incr incrCounter { i, Record { i, 0 } };
        verifier.Run (&incrCounter);
        verifier.Flush();
    }


    /*
    // read all the counters
    for (uint64_t i = 0 ; i < KeyCount ; ++i) {
        Get getCounter { i, Record { i, 1 } };
        verifier.Run (&getCounter);
        verifier.Flush();
        REQUIRE(getCounter.GetOutput() == 1);
    }
    */
}
