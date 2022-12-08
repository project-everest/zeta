

#ifndef __ZetaFormats_H
#define __ZetaFormats_H

#include "krmllib.h"



#include "ZetaFormatsApplicationTypes.h"
typedef struct LowParse_Slice_slice_s
{
  uint8_t *base;
  uint32_t len;
}
LowParse_Slice_slice;

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

typedef struct Zeta_Steel_LogEntry_Types_timestamp_s
{
  uint32_t epoch;
  uint32_t counter;
}
Zeta_Steel_LogEntry_Types_timestamp;

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

typedef struct Zeta_Steel_LogEntry_Types_evictM_payload_s
{
  uint16_t s;
  uint16_t s_;
}
Zeta_Steel_LogEntry_Types_evictM_payload;

typedef struct Zeta_Steel_LogEntry_Types_evictB_payload_s
{
  uint16_t s1;
  Zeta_Steel_LogEntry_Types_timestamp t;
}
Zeta_Steel_LogEntry_Types_evictB_payload;

typedef struct Zeta_Steel_LogEntry_Types_evictBM_payload_s
{
  uint16_t s2;
  uint16_t s_1;
  Zeta_Steel_LogEntry_Types_timestamp t1;
}
Zeta_Steel_LogEntry_Types_evictBM_payload;

typedef struct Zeta_Steel_LogEntry_Types_runApp_payload_s
{
  uint8_t fid;
  uint32_t rest;
}
Zeta_Steel_LogEntry_Types_runApp_payload;

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

typedef struct Zeta_Steel_LogEntry_Types_record_s
{
  Zeta_Steel_LogEntry_Types_key fst;
  Zeta_Steel_LogEntry_Types_value snd;
}
Zeta_Steel_LogEntry_Types_record;

#define Zeta_Steel_LogEntry_Types_AddM 0
#define Zeta_Steel_LogEntry_Types_AddB 1
#define Zeta_Steel_LogEntry_Types_RunApp 2
#define Zeta_Steel_LogEntry_Types_EvictM 3
#define Zeta_Steel_LogEntry_Types_EvictB 4
#define Zeta_Steel_LogEntry_Types_EvictBM 5
#define Zeta_Steel_LogEntry_Types_NextEpoch 6
#define Zeta_Steel_LogEntry_Types_VerifyEpoch 7

typedef uint8_t Zeta_Steel_LogEntry_Types_log_entry_tags;

typedef struct Zeta_Steel_LogEntry_Types_log_entry_s
{
  Zeta_Steel_LogEntry_Types_log_entry_tags tag;
  union {
    struct
    {
      uint16_t s;
      uint16_t s_;
      Zeta_Steel_LogEntry_Types_record r;
    }
    case_AddM;
    struct
    {
      uint16_t s;
      Zeta_Steel_LogEntry_Types_timestamp ts;
      uint16_t tid;
      Zeta_Steel_LogEntry_Types_record r;
    }
    case_AddB;
    Zeta_Steel_LogEntry_Types_runApp_payload case_RunApp;
    Zeta_Steel_LogEntry_Types_evictM_payload case_EvictM;
    Zeta_Steel_LogEntry_Types_evictB_payload case_EvictB;
    Zeta_Steel_LogEntry_Types_evictBM_payload case_EvictBM;
  }
  ;
}
Zeta_Steel_LogEntry_Types_log_entry;

typedef struct Zeta_Steel_LogEntry_Types_stamped_record_s
{
  Zeta_Steel_LogEntry_Types_record record;
  Zeta_Steel_LogEntry_Types_timestamp timestamp;
  uint16_t thread_id;
}
Zeta_Steel_LogEntry_Types_stamped_record;

uint32_t zeta__runapp_payload_offset(Zeta_Steel_LogEntry_Types_log_entry e);

typedef struct K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t_s
{
  Zeta_Steel_LogEntry_Types_log_entry fst;
  uint32_t snd;
}
K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t;

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t v;
}
FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t;

FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t
zeta__parser_log_entry(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

uint32_t
zeta__serialize_stamped_record(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_stamped_record v
);

uint32_t
zeta__serialize_value(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_value v
);

typedef struct K___Zeta_Steel_KeyUtils_u256_uint32_t_s
{
  Zeta_Steel_KeyUtils_u256 fst;
  uint32_t snd;
}
K___Zeta_Steel_KeyUtils_u256_uint32_t;

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___Zeta_Steel_KeyUtils_u256_uint32_t v;
}
FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t;

FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t
zeta__parser_u256(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

uint32_t
zeta__serialize_timestamp(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_timestamp v
);

extern uint32_t
Zeta_Formats_Aux_Application_key_Size_application_key_size32(
  Zeta_Steel_ApplicationTypes_key_type uu___
);

extern uint64_t
Zeta_Formats_Aux_Application_key_Low_application_key_validator(
  LowParse_Slice_slice x0,
  uint64_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_jumper(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern Zeta_Steel_ApplicationTypes_key_type
Zeta_Formats_Aux_Application_key_Low_application_key_reader(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_lserializer(
  Zeta_Steel_ApplicationTypes_key_type uu___,
  uint8_t *x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Size_application_value_size32(
  Zeta_Steel_ApplicationTypes_value_type uu___
);

extern uint64_t
Zeta_Formats_Aux_Application_value_Low_application_value_validator(
  LowParse_Slice_slice x0,
  uint64_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_jumper(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern Zeta_Steel_ApplicationTypes_value_type
Zeta_Formats_Aux_Application_value_Low_application_value_reader(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_lserializer(
  Zeta_Steel_ApplicationTypes_value_type uu___,
  uint8_t *x0,
  uint32_t x1
);


#define __ZetaFormats_H_DEFINED
#endif
