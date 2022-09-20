

#ifndef __Zeta_Steel_Application_H
#define __Zeta_Steel_Application_H

#include "krmllib.h"




typedef struct Zeta_Steel_KeyUtils_u256_s
{
  uint64_t v3;
  uint64_t v2;
  uint64_t v1;
  uint64_t v0;
}
Zeta_Steel_KeyUtils_u256;

typedef struct Zeta_Steel_KeyUtils_raw_key_s
{
  Zeta_Steel_KeyUtils_u256 k;
  uint16_t significant_digits;
}
Zeta_Steel_KeyUtils_raw_key;

typedef struct Zeta_Steel_LogEntry_Types_runApp_payload_s
{
  uint8_t fid;
  uint32_t rest;
}
Zeta_Steel_LogEntry_Types_runApp_payload;

typedef struct Zeta_Steel_VerifierTypes_thread_state_t_s
Zeta_Steel_VerifierTypes_thread_state_t;

typedef void *Zeta_Steel_Application_n_out_bytes;

#define Zeta_Steel_Application_Run_app_parsing_failure 0
#define Zeta_Steel_Application_Run_app_verify_failure 1
#define Zeta_Steel_Application_Run_app_success 2

typedef uint8_t Zeta_Steel_Application_verify_runapp_result_tags;

typedef struct Zeta_Steel_Application_verify_runapp_result_s
{
  Zeta_Steel_Application_verify_runapp_result_tags tag;
  uint32_t wrote;
}
Zeta_Steel_Application_verify_runapp_result;

bool
Zeta_Steel_Application_uu___is_Run_app_parsing_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
);

bool
Zeta_Steel_Application_uu___is_Run_app_verify_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
);

bool
Zeta_Steel_Application_uu___is_Run_app_success(
  Zeta_Steel_Application_verify_runapp_result projectee
);

Zeta_Steel_Application_verify_runapp_result
Zeta_Steel_Application_run_app_function(
  uint32_t log_len,
  Zeta_Steel_LogEntry_Types_runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  Zeta_Steel_VerifierTypes_thread_state_t t
);

Zeta_Steel_KeyUtils_raw_key Zeta_Steel_Application_key_type_to_base_key(uint64_t k);


#define __Zeta_Steel_Application_H_DEFINED
#endif
