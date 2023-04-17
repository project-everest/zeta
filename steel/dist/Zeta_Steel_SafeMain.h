

#ifndef __Zeta_Steel_SafeMain_H
#define __Zeta_Steel_SafeMain_H

#include "krmllib.h"

#include "steel_atomics.h"
#include "zeta_application.h"

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags;

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

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_Verifier_verify_result v;
}
FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result;

bool Zeta_Steel_SafeMain_check_verify_input(uint16_t tid, uint32_t len);

FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
Zeta_Steel_SafeMain_verify_log(
  uint16_t tid,
  uint32_t len,
  uint32_t out_len,
  uint8_t *input,
  uint8_t *output
);

Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
Zeta_Steel_SafeMain_max_certified_epoch(void);


#define __Zeta_Steel_SafeMain_H_DEFINED
#endif
