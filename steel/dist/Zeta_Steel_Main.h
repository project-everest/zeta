

#ifndef __Zeta_Steel_Main_H
#define __Zeta_Steel_Main_H

#include "krmllib.h"



#include "steel_atomics.h"
#include "zeta_application.h"
static inline bool Steel_ST_Reference_cas_u32(uint32_t *r, uint32_t v_old, uint32_t v_new);

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

#define Zeta_Steel_LogEntry_Types_Vfalse 0
#define Zeta_Steel_LogEntry_Types_Vtrue 1

typedef uint8_t Zeta_Steel_LogEntry_Types_vbool;

typedef struct Zeta_Steel_LogEntry_Types_descendent_hash_desc_s
{
  Zeta_Steel_KeyUtils_raw_key dhd_key;
  Zeta_Steel_KeyUtils_u256 dhd_h;
  Zeta_Steel_LogEntry_Types_vbool evicted_to_blum;
}
Zeta_Steel_LogEntry_Types_descendent_hash_desc;

#define Zeta_Steel_LogEntry_Types_Dh_vnone 0
#define Zeta_Steel_LogEntry_Types_Dh_vsome 1

typedef uint8_t Zeta_Steel_LogEntry_Types_descendent_hash_tags;

typedef struct Zeta_Steel_LogEntry_Types_descendent_hash_s
{
  Zeta_Steel_LogEntry_Types_descendent_hash_tags tag;
  Zeta_Steel_LogEntry_Types_descendent_hash_desc _0;
}
Zeta_Steel_LogEntry_Types_descendent_hash;

typedef struct Zeta_Steel_LogEntry_Types_mval_value_s
{
  Zeta_Steel_LogEntry_Types_descendent_hash l;
  Zeta_Steel_LogEntry_Types_descendent_hash r;
}
Zeta_Steel_LogEntry_Types_mval_value;

#define Zeta_Steel_LogEntry_Types_InternalKey 0
#define Zeta_Steel_LogEntry_Types_ApplicationKey 1

typedef uint8_t Zeta_Steel_LogEntry_Types_key_tags;

typedef struct Zeta_Steel_LogEntry_Types_key_s
{
  Zeta_Steel_LogEntry_Types_key_tags tag;
  union {
    Zeta_Steel_KeyUtils_raw_key case_InternalKey;
    Zeta_Steel_ApplicationTypes_key_type case_ApplicationKey;
  }
  ;
}
Zeta_Steel_LogEntry_Types_key;

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags;

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_ApplicationTypes_value_type v;
}
FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type;

#define Zeta_Steel_LogEntry_Types_MValue 0
#define Zeta_Steel_LogEntry_Types_DValue 1

typedef uint8_t Zeta_Steel_LogEntry_Types_value_tags;

typedef struct Zeta_Steel_LogEntry_Types_value_s
{
  Zeta_Steel_LogEntry_Types_value_tags tag;
  union {
    Zeta_Steel_LogEntry_Types_mval_value case_MValue;
    FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type case_DValue;
  }
  ;
}
Zeta_Steel_LogEntry_Types_value;

#define Zeta_Steel_AggregateEpochHashes_Read_max_error 0
#define Zeta_Steel_AggregateEpochHashes_Read_max_none 1
#define Zeta_Steel_AggregateEpochHashes_Read_max_some 2

typedef uint8_t Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_tags;

typedef struct Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_s
{
  Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_tags tag;
  uint32_t _0;
}
Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result;

typedef struct Zeta_Steel_VerifierTypes_thread_state_t_s
Zeta_Steel_VerifierTypes_thread_state_t;

typedef struct Zeta_Steel_VerifierTypes_kv_s
{
  Zeta_Steel_LogEntry_Types_key key;
  Zeta_Steel_LogEntry_Types_value value;
}
Zeta_Steel_VerifierTypes_kv;

#define Zeta_Steel_Verifier_Parsing_failure 0
#define Zeta_Steel_Verifier_App_failure 1
#define Zeta_Steel_Verifier_Verify_entry_failure 2
#define Zeta_Steel_Verifier_Verify_success 3

typedef uint8_t Zeta_Steel_Verifier_verify_result_tags;

typedef struct Zeta_Steel_Verifier_verify_result_s
{
  Zeta_Steel_Verifier_verify_result_tags tag;
  union {
    uint32_t case_Parsing_failure;
    uint32_t case_App_failure;
    uint32_t case_Verify_entry_failure;
    struct
    {
      uint32_t read;
      uint32_t wrote;
    }
    case_Verify_success;
  }
  ;
}
Zeta_Steel_Verifier_verify_result;

typedef struct Zeta_Steel_Main_top_level_state_s Zeta_Steel_Main_top_level_state;

Zeta_Steel_Main_top_level_state *Zeta_Steel_Main_init();

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_Verifier_verify_result v;
}
FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result;

FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
Zeta_Steel_Main_verify_log(
  Zeta_Steel_Main_top_level_state *r,
  uint16_t tid,
  uint32_t len,
  uint8_t *input,
  uint32_t out_len,
  uint8_t *output
);

Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
Zeta_Steel_Main_max_certified_epoch(Zeta_Steel_Main_top_level_state *r);

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_VerifierTypes_kv v;
}
FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv;

FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv
Zeta_Steel_Main_read_store(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t slot);

void
Zeta_Steel_Main_write_store(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t slot,
  Zeta_Steel_LogEntry_Types_value v
);


#define __Zeta_Steel_Main_H_DEFINED
#endif
