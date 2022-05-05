#include <assert.h>
#include <verifier_proxy.h>
#include <Zeta_Steel_Main.h>

typedef FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result zeta_res_t;
typedef Zeta_Steel_Main_top_level_state top_state_t;

top_state_t *verifier_state = NULL;

void verifier_init()
{
    verifier_state = Zeta_Steel_Main_init();
}

int verifier_verify_log (uint8_t threadId,
                         uint8_t *inp,
                         size_t inpLen,
                         uint8_t *out,
                         size_t outBufSize,
                         size_t *outLen)
{
    zeta_res_t rc = Zeta_Steel_Main_verify_log(verifier_state,
                                               threadId,
                                               inpLen,
                                               inp,
                                               outBufSize,
                                               out);

    if (rc.tag == FStar_Pervasives_Native_None) {
        return -1;
    }

    assert (rc.tag == FStar_Pervasives_Native_Some);

    if (rc.v.tag != Zeta_Steel_Verifier_Verify_success) {
        return -1;
    }

    *outLen = rc.v.case_Verify_success.wrote;

    return 0;
}
