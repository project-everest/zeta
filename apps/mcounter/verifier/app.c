#include <Zeta_Steel_Main.h>
#include <Zeta_Steel_Main.c>
#include <krml_bridge.h>

bool
Zeta_Steel_ApplicationTypes_eq_value_type(
  Zeta_Steel_ApplicationTypes_value_type v0,
  Zeta_Steel_ApplicationTypes_value_type v1
)
{
    return v0 == v1;
}

Zeta_Steel_LogEntry_Types_base_key
Zeta_Steel_Application_key_type_to_base_key(Zeta_Steel_ApplicationTypes_key_type k)
{
    Zeta_Steel_LogEntry_Types_base_key bk =
    {
        .significant_digits = 256,
        .k = { .v0 = k,
               .v1 = 0,
               .v2 = 0,
               .v3 = 0
        }
    };

    return bk;
}

verify_runapp_result new_counter (uint8_t *base,
                                  uint32_t len,
                                  uint32_t out_len,
                                  uint32_t out_offset,
                                  uint8_t *out,
                                  Zeta_Steel_VerifierTypes_thread_state_t t)
{
    kb_new_p param = kb_new_p_reader(base, len, 0);
    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv entry =
        Zeta_Steel_Main_read_store(t, param.s);

    /* check: slot != empty */
    if (entry.tag == FStar_Pervasives_Native_None) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    /* check slot contains app-key & val */
    if (entry.v.value.tag != Zeta_Steel_LogEntry_Types_DValue) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    /* check value is null */
    if (entry.v.value.case_DValue.tag != FStar_Pervasives_Native_None) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    Zeta_Steel_LogEntry_Types_value new_val = {
        .tag = entry.v.value.tag,
        .case_DValue = {
            .tag = FStar_Pervasives_Native_Some,
            .v = 0
        }
    };

    Zeta_Steel_Main_write_store (t, param.s, new_val);

    return (verify_runapp_result) { .tag = Run_app_success, .wrote = 0 };
}


verify_runapp_result
Zeta_Steel_Application_run_app_function(
  runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  Zeta_Steel_VerifierTypes_thread_state_t t
)
{
    uint8_t *log_param_base = log_array + pl_pos;

    switch (pl.fid) {
    case 0:
        return new_counter(log_param_base, pl.rest, out_len, out_offset, out, t);
        break;

    default:
        break;
    }

    return (verify_runapp_result)
    {
        .tag = Run_app_verify_failure,
        .wrote = 0
    };
}
