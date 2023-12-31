#include <assert.h>
#include <stdio.h>

#include <openenclave/host.h>

#include <verifier_proxy.h>
#include <zeta_config.h>
#include <Zeta_Steel_Main.h>

#include "enclave_u.h"

oe_enclave_t* enclave = NULL;


void verifier_init(const char *type, uint32_t flags) 
{
    oe_result_t result;
    result = oe_create_enclave_enclave(
        type, OE_ENCLAVE_TYPE_AUTO, flags, NULL, 0, &enclave);
    if (result != OE_OK)
    {
        fprintf(
            stderr,
            "oe_create_openenclave_enclave_enclave(): result=%u (%s)\n",
            result,
            oe_result_str(result));
        if (enclave)
            oe_terminate_enclave(enclave);

        return;
    }

    result = enclave_Zeta_Steel_Main_init(enclave);
    fprintf( stdout, "Host: enclave initialized\n");
    return ;
}

int verifier_verify_log (uint8_t threadId,
                         uint8_t *inp,
                         size_t inpLen,
                         uint8_t *out,
                         size_t outBufSize,
                         size_t *outLen)
{

    oe_result_t result;
    enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result rc;

    result = enclave_Zeta_Steel_Main_verify_log(enclave, &rc, threadId, inpLen, inp, outBufSize, out);
    fprintf(stdout, "Host: returned from enclave \n");

    if (rc.tag == FStar_Pervasives_Native_None) {
        return VRC_VerificationFailure;
    }

    assert (rc.tag == FStar_Pervasives_Native_Some);

    if (rc.v.tag != Zeta_Steel_Verifier_Verify_success) {
        return (int) rc.v.tag;
    }
 
    *outLen = rc.v.dummy.case_Verify_success.wrote;
    return VRC_Success;
}

void verifier_terminate()
{
    if (enclave)
        oe_terminate_enclave(enclave);
    fprintf(stdout, "Host: cleaned up enclave \n");

    return;
}