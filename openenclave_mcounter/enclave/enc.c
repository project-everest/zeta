
#include <stdio.h>
#include "openenclave_mcounter_t.h"
#include<app.c>

Zeta_Steel_Main_top_level_state* verifier_state = NULL;

enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result convert(FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result rc);

void enclave_Zeta_Steel_Main_init()
{

    fprintf(stdout, "Enclave: Calling Zeta_Steel_Main_init() in enclave\n");
    verifier_state = Zeta_Steel_Main_init();
    if (verifier_state == NULL)
    {
        fprintf(stdout, "Enclave: Init failed, state is NULL\n");
    }
    return;  
}

enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result enclave_Zeta_Steel_Main_verify_log( uint16_t tid,
    uint32_t len,
    uint8_t* input,
    uint32_t out_len,
    uint8_t* output
) 
{
    fprintf(stdout, "Enclave: Calling Zeta_Steel_Main_verify_log() in enclave\n");
    FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result rc = Zeta_Steel_Main_verify_log(verifier_state, tid, len, input, out_len, output);
    enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result enclave_rc = convert(rc);
    return enclave_rc;
}

enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result convert(FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result rc)
{
    enclave_FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result enc_rc;

    enc_rc.tag = rc.tag;
    enc_rc.v.tag = rc.v.tag;
    enc_rc.v.dummy.case_Verify_success.read = rc.v.case_Verify_success.read;
    enc_rc.v.dummy.case_Verify_success.wrote = rc.v.case_Verify_success.wrote;

    return enc_rc;
}