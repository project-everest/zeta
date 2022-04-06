#include <Zeta_Steel_Main.c>

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
    verify_runapp_result res =
    {
        .tag = Run_app_verify_failure,
        .wrote = 0
    };

    return res;
}
