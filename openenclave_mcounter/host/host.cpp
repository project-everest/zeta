// Copyright (c) Open Enclave SDK contributors.
// Licensed under the MIT License.
//#define CATCH_CONFIG_MAIN

#include <stdio.h>
#include <openenclave/host.h>

#include <verifier_proxy.h>
#include <zeta_config.h>
// #include <Zeta_Steel_Main.h>  // remove

// #include <catch2/catch.hpp>

#include <app.h>
#include <trace.h>
#include <verifier_proxy.h>
#include <verifier_stub.h>

using namespace Zeta;
using namespace Zeta::mcounter;

static VerifierProxy GetVerifierProxy(const char *type, uint32_t flags)
{
    verifier_init(type, flags);
    VerifierProxy proxy{ &verifier_verify_log };
    return proxy;
}

// Include the untrusted openenclave_mcounter header that is generated
// during the build. This file is generated by calling the
// sdk tool oeedger8r against the openenclave_mcounter.edl file.

bool check_simulate_opt(int* argc, const char* argv[])
{
    for (int i = 0; i < *argc; i++)
    {
        if (strcmp(argv[i], "--simulate") == 0)
        {
            fprintf(stdout, "Running in simulation mode\n");
            memmove(&argv[i], &argv[i + 1], (*argc - i) * sizeof(char*));
            (*argc)--;
            return true;
        }
    }
    return false;
}


int main(int argc, const char* argv[])
{
    int ret = 1;

    uint32_t flags = OE_ENCLAVE_FLAG_DEBUG;
    if (check_simulate_opt(&argc, argv))
    {
        flags |= OE_ENCLAVE_FLAG_SIMULATE;
    }

    if (argc != 2)
    {
        fprintf(
            stderr, "Usage: %s enclave_image_path [ --simulate  ]\n", argv[0]);
        return ret;
    }

 
    auto proxy = GetVerifierProxy(argv[1], flags);

    VerifierStub verifier{ 0, proxy };

    Record record{ 0 };
    App_key_app_key k = 0;
    New_Counter newCounter{ &k, &record };

    verifier.Run(&newCounter);
    fprintf(stdout, "Host: returned from verifier.Run\n");
    verifier.Flush();

    //result = enclave_Zeta_Steel_Main_init(enclave);
    //enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result enclave_rc;
/*
    result = enclave_Zeta_Steel_Main_verify_log(enclave, &enclave_rc, 0, 0, NULL, 0, NULL);
    FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result rc = convert(enclave_rc);
    char input[] = "hello", output[6];
    result = enclave_strrev(enclave, input, 5, output, 5);
    fprintf(stdout, "return from strrev\n");
    fprintf(stdout, output);
*/
    ret = 0;

   // Clean up the enclave if we created one
    // if (enclave)
        // oe_terminate_enclave(enclave);

    return ret;
}

/*
TEST_CASE("test single function (newcounter)")
{
    auto proxy = GetVerifierProxy();

    VerifierStub verifier{ 0, proxy };

    New newCounter{ 0, Record { 0} };
    verifier.Run(&newCounter);
    verifier.Flush();
}
*/

