#include <ZetaFormatsApplicationTypes.h>
#include <Zeta_Steel_Main.h>
#include <Zeta_Steel_Main.c>
#include <stdint.h>
#include <New_p.h>
#include <Incr_p.h>
#include <Get_p.h>
#include <App_val.h>

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
    LowParse_Slice_slice sl = { .base = base, .len = len };

    New_p_new_p param = New_p_new_p_reader(sl, 0);

    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv entry =
        Zeta_Steel_Main_read_store(t, param.s);

    /* check: slot is empty */
    if (entry.tag != FStar_Pervasives_Native_None) {
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

verify_runapp_result incr_counter (uint8_t *base,
                                   uint32_t len,
                                   uint32_t out_len,
                                   uint32_t out_offset,
                                   uint8_t *out,
                                   Zeta_Steel_VerifierTypes_thread_state_t t)
{
    LowParse_Slice_slice sl = { .base = base, .len = len };

    Incr_p_incr_p param = Incr_p_incr_p_reader(sl, 0);

    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv entry =
        Zeta_Steel_Main_read_store(t, param.s);

    /* check: slot is not empty */
    if (entry.tag == FStar_Pervasives_Native_None) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    /* check slot contains app-key & val */
    if (entry.v.value.tag != Zeta_Steel_LogEntry_Types_DValue) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    app_val_t old_val = entry.v.value.case_DValue.v;

    Zeta_Steel_LogEntry_Types_value new_val = {
        .tag = entry.v.value.tag,
        .case_DValue = {
            .tag = FStar_Pervasives_Native_Some,
            .v = old_val + 1
        }
    };

    Zeta_Steel_Main_write_store (t, param.s, new_val);

    /* write the output */
    uint32_t wrote = App_val_app_val_lserializer(old_val, out, out_offset);

    return (verify_runapp_result) { .tag = Run_app_success, .wrote = wrote };
}

verify_runapp_result get_counter (uint8_t *base,
                                  uint32_t len,
                                  uint32_t out_len,
                                  uint32_t out_offset,
                                  uint8_t *out,
                                  Zeta_Steel_VerifierTypes_thread_state_t t)
{
    LowParse_Slice_slice sl = { .base = base, .len = len };

    Get_p_get_p param = Get_p_get_p_reader(sl, 0);

    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv entry =
        Zeta_Steel_Main_read_store(t, param.s);

    /* check: slot is not empty */
    if (entry.tag == FStar_Pervasives_Native_None) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    /* check slot contains app-key & val */
    if (entry.v.value.tag != Zeta_Steel_LogEntry_Types_DValue) {
        return (verify_runapp_result) { .tag = Run_app_verify_failure, .wrote = 0 };
    }

    app_val_t val = entry.v.value.case_DValue.v;

    /* write the output */
    uint32_t wrote = App_val_app_val_lserializer(val, out, out_offset);

    return (verify_runapp_result) { .tag = Run_app_success, .wrote = wrote };
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

    case 1:
        return incr_counter(log_param_base, pl.rest, out_len, out_offset, out, t);

    case 2:
        return get_counter(log_param_base, pl.rest, out_len, out_offset, out, t);

    default:
        break;
    }

    return (verify_runapp_result)
    {
        .tag = Run_app_verify_failure,
        .wrote = 0
    };
}
