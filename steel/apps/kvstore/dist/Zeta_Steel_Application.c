

#include "Zeta_Steel_Application.h"

typedef uint8_t *byte_array;

typedef struct vget_args_t_s
{
  uint64_t vget_key;
  uint64_t vget_value;
  uint16_t vget_slot;
}
vget_args_t;

typedef struct __Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t_s
{
  vget_args_t fst;
  uint32_t snd;
}
__Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t;

#define None 0
#define Some 1

typedef uint8_t option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags;

typedef struct option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  __Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t v;
}
option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t;

extern option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t
kvstore_vget_args_parser(uint32_t x0, uint32_t x1, uint32_t x2, uint8_t *x3);

typedef struct vput_args_t_s
{
  uint64_t vput_key;
  uint64_t vput_value;
  uint16_t vput_slot;
}
vput_args_t;

typedef struct __Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t_s
{
  vput_args_t fst;
  uint32_t snd;
}
__Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t;

typedef struct option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  __Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t v;
}
option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t;

extern option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t
kvstore_vput_args_parser(uint32_t x0, uint32_t x1, uint32_t x2, uint8_t *x3);

static uint8_t vget_id = 0U;

static uint8_t vput_id = 1U;

static uint16_t store_size = 16U;

typedef uint32_t uninterpreted;

typedef struct timestamp_s
{
  uint32_t epoch;
  uint32_t counter;
}
timestamp;

#define Vfalse 0
#define Vtrue 1

typedef uint8_t vbool;

typedef struct descendent_hash_desc_s
{
  Zeta_Steel_KeyUtils_raw_key dhd_key;
  Zeta_Steel_KeyUtils_u256 dhd_h;
  vbool evicted_to_blum;
}
descendent_hash_desc;

#define Dh_vnone 0
#define Dh_vsome 1

typedef uint8_t descendent_hash_tags;

typedef struct descendent_hash_s
{
  descendent_hash_tags tag;
  descendent_hash_desc _0;
}
descendent_hash;

typedef struct mval_value_s
{
  descendent_hash l;
  descendent_hash r;
}
mval_value;

#define InternalKey 0
#define ApplicationKey 1

typedef uint8_t key_tags;

typedef struct key_s
{
  key_tags tag;
  union {
    Zeta_Steel_KeyUtils_raw_key case_InternalKey;
    uint64_t case_ApplicationKey;
  }
  ;
}
key;

typedef struct option__uint64_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  uint64_t v;
}
option__uint64_t;

#define MValue 0
#define DValue 1

typedef uint8_t value_tags;

typedef struct value_s
{
  value_tags tag;
  union {
    mval_value case_MValue;
    option__uint64_t case_DValue;
  }
  ;
}
value;

#define MAdd 0
#define BAdd 1

typedef uint8_t add_method;

typedef struct option__uint16_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  uint16_t v;
}
option__uint16_t;

typedef struct __uint16_t_bool_s
{
  uint16_t fst;
  bool snd;
}
__uint16_t_bool;

typedef struct option__uint16_t___bool_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  __uint16_t_bool v;
}
option__uint16_t___bool;

typedef struct store_entry_s
{
  key key;
  value value;
  add_method add_method;
  option__uint16_t l_child_in_store;
  option__uint16_t r_child_in_store;
  option__uint16_t___bool parent_slot;
}
store_entry;

#define None0 0
#define Some0 1

typedef uint8_t high_water_mark_tags;

typedef struct high_water_mark_s
{
  high_water_mark_tags tag;
  uint32_t v;
}
high_water_mark;

typedef struct ha_s
{
  uint8_t *acc;
  uint32_t *ctr;
  uint8_t *tmp;
}
ha;

typedef struct epoch_hashes_t_s
{
  ha hadd;
  ha hevict;
}
epoch_hashes_t;

typedef struct __uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  uint32_t fst;
  epoch_hashes_t snd;
}
__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  __uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t v;
}
option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  size_t store_len;
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *store;
}
tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct all_epoch_hashes_s
{
  tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t etbl;
  high_water_mark *high;
}
all_epoch_hashes;

typedef struct hasher_t_s
{
  uint8_t *serialization_buffer;
  uint8_t *hash_buffer;
}
hasher_t;

typedef struct option__Zeta_Steel_ThreadStateModel_store_entry_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  store_entry v;
}
option__Zeta_Steel_ThreadStateModel_store_entry;

typedef option__Zeta_Steel_ThreadStateModel_store_entry *vstore;

typedef struct Zeta_Steel_VerifierTypes_thread_state_t_s
{
  uint16_t thread_id;
  bool *failed;
  option__Zeta_Steel_ThreadStateModel_store_entry *store;
  timestamp *clock;
  Zeta_Steel_KeyUtils_raw_key *last_evict_key;
  all_epoch_hashes epoch_hashes;
  high_water_mark *last_verified_epoch;
  uint8_t *serialization_buffer;
  uint8_t *iv_buffer;
  hasher_t hasher;
}
Zeta_Steel_VerifierTypes_thread_state_t;

typedef struct kv_s
{
  key key;
  value value;
}
kv;

bool
Zeta_Steel_Application_uu___is_Run_app_parsing_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
)
{
  if (projectee.tag == Zeta_Steel_Application_Run_app_parsing_failure)
    return true;
  else
    return false;
}

bool
Zeta_Steel_Application_uu___is_Run_app_verify_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
)
{
  if (projectee.tag == Zeta_Steel_Application_Run_app_verify_failure)
    return true;
  else
    return false;
}

bool
Zeta_Steel_Application_uu___is_Run_app_success(
  Zeta_Steel_Application_verify_runapp_result projectee
)
{
  if (projectee.tag == Zeta_Steel_Application_Run_app_success)
    return true;
  else
    return false;
}

typedef struct __uint64_t_FStar_Pervasives_Native_option__uint64_t_s
{
  uint64_t fst;
  option__uint64_t snd;
}
__uint64_t_FStar_Pervasives_Native_option__uint64_t;

static uint64_t
fst__uint64_t_FStar_Pervasives_Native_option_uint64_t(
  __uint64_t_FStar_Pervasives_Native_option__uint64_t x
)
{
  return x.fst;
}

static option__uint64_t
snd__uint64_t_FStar_Pervasives_Native_option_uint64_t(
  __uint64_t_FStar_Pervasives_Native_option__uint64_t x
)
{
  return x.snd;
}

static bool
__eq__FStar_Pervasives_Native_option__uint64_t(option__uint64_t y, option__uint64_t x)
{
  if (x.tag == None)
    if (y.tag == None)
      return true;
    else
      return false;
  else if (x.tag == Some)
  {
    uint64_t x_v = x.v;
    if (y.tag == Some)
    {
      uint64_t y_v = y.v;
      return true && y_v == x_v;
    }
    else
      return false;
  }
  else
    return false;
}

static bool
vget_impl(vget_args_t r, __uint64_t_FStar_Pervasives_Native_option__uint64_t store_kv)
{
  if (r.vget_key == fst__uint64_t_FStar_Pervasives_Native_option_uint64_t(store_kv))
    if
    (
      __eq__FStar_Pervasives_Native_option__uint64_t((
          (option__uint64_t){ .tag = Some, .v = r.vget_value }
        ),
        snd__uint64_t_FStar_Pervasives_Native_option_uint64_t(store_kv))
    )
      return true;
    else
      return false;
  else
    return false;
}

typedef struct option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  __uint64_t_FStar_Pervasives_Native_option__uint64_t v;
}
option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t;

typedef struct option__Zeta_Steel_VerifierTypes_kv_s
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_tags tag;
  kv v;
}
option__Zeta_Steel_VerifierTypes_kv;

static Zeta_Steel_Application_verify_runapp_result
run_vget(
  uint32_t log_len,
  Zeta_Steel_LogEntry_Types_runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  Zeta_Steel_VerifierTypes_thread_state_t t
)
{
  option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t
  ropt = kvstore_vget_args_parser(log_len, pl_pos, pl.rest, log_array);
  if (ropt.tag == None)
    return
      (
        (Zeta_Steel_Application_verify_runapp_result){
          .tag = Zeta_Steel_Application_Run_app_parsing_failure
        }
      );
  else if (ropt.tag == Some)
  {
    uint32_t consumed = ropt.v.snd;
    vget_args_t r = ropt.v.fst;
    if (consumed == pl.rest)
      if (r.vget_slot < store_size)
      {
        option__Zeta_Steel_ThreadStateModel_store_entry se_opt = t.store[(size_t)r.vget_slot];
        option__Zeta_Steel_VerifierTypes_kv kvopt0;
        if (se_opt.tag == None)
          kvopt0 = ((option__Zeta_Steel_VerifierTypes_kv){ .tag = None });
        else if (se_opt.tag == Some)
        {
          store_entry se = se_opt.v;
          store_entry se1 = se;
          kvopt0 =
            (
              (option__Zeta_Steel_VerifierTypes_kv){
                .tag = Some,
                .v = { .key = se1.key, .value = se1.value }
              }
            );
        }
        else
          kvopt0 =
            KRML_EABORT(option__Zeta_Steel_VerifierTypes_kv,
              "unreachable (pattern matches are exhaustive in F*)");
        option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t kvopt;
        if
        (kvopt0.tag == Some && kvopt0.v.key.tag == ApplicationKey && kvopt0.v.value.tag == DValue)
        {
          option__uint64_t vopt = kvopt0.v.value.case_DValue;
          uint64_t k = kvopt0.v.key.case_ApplicationKey;
          kvopt =
            (
              (option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t){
                .tag = Some,
                .v = { .fst = k, .snd = vopt }
              }
            );
        }
        else
          kvopt = ((option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t){ .tag = None });
        if (kvopt.tag == None)
          return
            (
              (Zeta_Steel_Application_verify_runapp_result){
                .tag = Zeta_Steel_Application_Run_app_verify_failure
              }
            );
        else if (kvopt.tag == Some)
        {
          option__uint64_t vopt = kvopt.v.snd;
          uint64_t k = kvopt.v.fst;
          bool
          b =
            vget_impl(r,
              ((__uint64_t_FStar_Pervasives_Native_option__uint64_t){ .fst = k, .snd = vopt }));
          if (b)
          {
            uint32_t wrote = 0U;
            return
              (
                (Zeta_Steel_Application_verify_runapp_result){
                  .tag = Zeta_Steel_Application_Run_app_success,
                  .wrote = wrote
                }
              );
          }
          else
            return
              (
                (Zeta_Steel_Application_verify_runapp_result){
                  .tag = Zeta_Steel_Application_Run_app_verify_failure
                }
              );
        }
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      else
        return
          (
            (Zeta_Steel_Application_verify_runapp_result){
              .tag = Zeta_Steel_Application_Run_app_verify_failure
            }
          );
    else
      return
        (
          (Zeta_Steel_Application_verify_runapp_result){
            .tag = Zeta_Steel_Application_Run_app_parsing_failure
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static bool
vput_impl(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  vput_args_t r,
  __uint64_t_FStar_Pervasives_Native_option__uint64_t store_kv
)
{
  if (r.vput_key == fst__uint64_t_FStar_Pervasives_Native_option_uint64_t(store_kv))
  {
    option__Zeta_Steel_ThreadStateModel_store_entry se_opt = t.store[(size_t)r.vput_slot];
    if (se_opt.tag == Some)
    {
      store_entry se = se_opt.v;
      store_entry se1 = se;
      store_entry
      se_ =
        {
          .key = se1.key,
          .value = { .tag = DValue, { .case_DValue = { .tag = Some, .v = r.vput_value } } },
          .add_method = se1.add_method, .l_child_in_store = se1.l_child_in_store,
          .r_child_in_store = se1.r_child_in_store, .parent_slot = se1.parent_slot
        };
      t.store[(size_t)r.vput_slot] =
        ((option__Zeta_Steel_ThreadStateModel_store_entry){ .tag = Some, .v = se_ });
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
    return true;
  }
  else
    return false;
}

static Zeta_Steel_Application_verify_runapp_result
run_vput(
  uint32_t log_len,
  Zeta_Steel_LogEntry_Types_runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  Zeta_Steel_VerifierTypes_thread_state_t t
)
{
  option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t
  ropt = kvstore_vput_args_parser(log_len, pl_pos, pl.rest, log_array);
  if (ropt.tag == None)
    return
      (
        (Zeta_Steel_Application_verify_runapp_result){
          .tag = Zeta_Steel_Application_Run_app_parsing_failure
        }
      );
  else if (ropt.tag == Some)
  {
    uint32_t consumed = ropt.v.snd;
    vput_args_t r = ropt.v.fst;
    if (consumed == pl.rest)
      if (r.vput_slot < store_size)
      {
        option__Zeta_Steel_ThreadStateModel_store_entry se_opt = t.store[(size_t)r.vput_slot];
        option__Zeta_Steel_VerifierTypes_kv kvopt0;
        if (se_opt.tag == None)
          kvopt0 = ((option__Zeta_Steel_VerifierTypes_kv){ .tag = None });
        else if (se_opt.tag == Some)
        {
          store_entry se = se_opt.v;
          store_entry se1 = se;
          kvopt0 =
            (
              (option__Zeta_Steel_VerifierTypes_kv){
                .tag = Some,
                .v = { .key = se1.key, .value = se1.value }
              }
            );
        }
        else
          kvopt0 =
            KRML_EABORT(option__Zeta_Steel_VerifierTypes_kv,
              "unreachable (pattern matches are exhaustive in F*)");
        option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t kvopt;
        if
        (kvopt0.tag == Some && kvopt0.v.key.tag == ApplicationKey && kvopt0.v.value.tag == DValue)
        {
          option__uint64_t vopt = kvopt0.v.value.case_DValue;
          uint64_t k = kvopt0.v.key.case_ApplicationKey;
          kvopt =
            (
              (option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t){
                .tag = Some,
                .v = { .fst = k, .snd = vopt }
              }
            );
        }
        else
          kvopt = ((option__K___uint64_t_FStar_Pervasives_Native_option__uint64_t){ .tag = None });
        if (kvopt.tag == None)
          return
            (
              (Zeta_Steel_Application_verify_runapp_result){
                .tag = Zeta_Steel_Application_Run_app_verify_failure
              }
            );
        else if (kvopt.tag == Some)
        {
          option__uint64_t vopt = kvopt.v.snd;
          uint64_t k = kvopt.v.fst;
          bool
          b =
            vput_impl(t,
              r,
              ((__uint64_t_FStar_Pervasives_Native_option__uint64_t){ .fst = k, .snd = vopt }));
          if (b)
          {
            uint32_t wrote = 0U;
            return
              (
                (Zeta_Steel_Application_verify_runapp_result){
                  .tag = Zeta_Steel_Application_Run_app_success,
                  .wrote = wrote
                }
              );
          }
          else
            return
              (
                (Zeta_Steel_Application_verify_runapp_result){
                  .tag = Zeta_Steel_Application_Run_app_verify_failure
                }
              );
        }
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      else
        return
          (
            (Zeta_Steel_Application_verify_runapp_result){
              .tag = Zeta_Steel_Application_Run_app_verify_failure
            }
          );
    else
      return
        (
          (Zeta_Steel_Application_verify_runapp_result){
            .tag = Zeta_Steel_Application_Run_app_parsing_failure
          }
        );
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

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
)
{
  KRML_MAYBE_UNUSED_VAR(out_len);
  KRML_MAYBE_UNUSED_VAR(out_offset);
  KRML_MAYBE_UNUSED_VAR(out);
  if (pl.fid == vget_id)
    return run_vget(log_len, pl, pl_pos, log_array, t);
  else if (pl.fid == vput_id)
    return run_vput(log_len, pl, pl_pos, log_array, t);
  else
    return
      (
        (Zeta_Steel_Application_verify_runapp_result){
          .tag = Zeta_Steel_Application_Run_app_parsing_failure
        }
      );
}

Zeta_Steel_KeyUtils_raw_key Zeta_Steel_Application_key_type_to_base_key(uint64_t k)
{
  return
    (
      (Zeta_Steel_KeyUtils_raw_key){
        .k = { .v3 = 0ULL, .v2 = 0ULL, .v1 = 0ULL, .v0 = k },
        .significant_digits = 256U
      }
    );
}

