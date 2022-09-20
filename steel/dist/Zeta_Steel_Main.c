

#include "Zeta_Steel_Main.h"



typedef uint8_t *dtuple2___uint8_t____;

extern void
Hacl_Blake2b_32_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *_dummy
);

typedef uint32_t *lock_t;

static uint32_t *new_lock()
{
  uint32_t *r = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
  return r;
}

static uint32_t *fst___uint32_t____(uint32_t *x)
{
  return x;
}

static void acquire(uint32_t *l)
{
  bool b0 = Steel_ST_Reference_cas_u32(fst___uint32_t____(l), (uint32_t)0U, (uint32_t)1U);
  bool cond;
  if (b0)
    cond = false;
  else
    cond = true;
  while (cond)
  {
    bool b = Steel_ST_Reference_cas_u32(fst___uint32_t____(l), (uint32_t)0U, (uint32_t)1U);
    bool ite;
    if (b)
      ite = false;
    else
      ite = true;
    cond = ite;
  }
}

static void release(uint32_t *l)
{
  bool b = Steel_ST_Reference_cas_u32(fst___uint32_t____(l), (uint32_t)1U, (uint32_t)0U);
}

typedef struct cancellable_lock_s
{
  bool *lref;
  uint32_t *llock;
}
cancellable_lock;

static cancellable_lock new_cancellable_lock()
{
  KRML_CHECK_SIZE(sizeof (bool), (uint32_t)1U);
  bool *r = KRML_HOST_MALLOC(sizeof (bool));
  r[0U] = true;
  uint32_t *l = new_lock();
  return ((cancellable_lock){ .lref = r, .llock = l });
}

static bool acquire0(cancellable_lock c)
{
  acquire(c.llock);
  bool b = *c.lref;
  if (!b)
    release(c.llock);
  return b;
}

static void release0(cancellable_lock c)
{
  release(c.llock);
}

static void cancel(cancellable_lock c)
{
  KRML_HOST_FREE(c.lref);
}

extern bool
Zeta_Steel_ApplicationTypes_eq_value_type(
  Zeta_Steel_ApplicationTypes_value_type v0,
  Zeta_Steel_ApplicationTypes_value_type v1
);

extern uint16_t Zeta_Steel_ApplicationTypes_store_size;

extern uint32_t Zeta_Steel_ApplicationTypes_n_threads;

static bool eq_u256(Zeta_Steel_KeyUtils_u256 i0, Zeta_Steel_KeyUtils_u256 i1)
{
  return i0.v0 == i1.v0 && i0.v1 == i1.v1 && i0.v2 == i1.v2 && i0.v3 == i1.v3;
}

typedef struct __uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
__uint32_t_uint32_t;

static __uint32_t_uint32_t bit_offset_in_word(uint16_t i)
{
  if (i < (uint16_t)64U)
    return ((__uint32_t_uint32_t){ .fst = (uint32_t)0U, .snd = (uint32_t)i });
  else if (i < (uint16_t)128U)
    return ((__uint32_t_uint32_t){ .fst = (uint32_t)1U, .snd = (uint32_t)(i - (uint16_t)64U) });
  else if (i < (uint16_t)192U)
    return ((__uint32_t_uint32_t){ .fst = (uint32_t)2U, .snd = (uint32_t)(i - (uint16_t)128U) });
  else
    return ((__uint32_t_uint32_t){ .fst = (uint32_t)3U, .snd = (uint32_t)(i - (uint16_t)192U) });
}

static uint64_t truncate_word(uint64_t k, uint32_t index)
{
  if (index == (uint32_t)0U)
    return (uint64_t)0U;
  else
  {
    uint32_t shift_index = (uint32_t)64U - index;
    uint64_t mask = (uint64_t)0xffffffffffffffffU >> shift_index;
    return k & mask;
  }
}

static Zeta_Steel_KeyUtils_raw_key truncate_key(Zeta_Steel_KeyUtils_raw_key k, uint16_t w)
{
  if (w == (uint16_t)256U)
    return k;
  else
  {
    __uint32_t_uint32_t scrut = bit_offset_in_word(w);
    uint32_t word = scrut.fst;
    uint32_t index = scrut.snd;
    Zeta_Steel_KeyUtils_u256 kk = k.k;
    Zeta_Steel_KeyUtils_u256 kk_;
    if (word == (uint32_t)0U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = (uint64_t)0U,
            .v2 = (uint64_t)0U,
            .v1 = (uint64_t)0U,
            .v0 = truncate_word(kk.v0, index)
          }
        );
    else if (word == (uint32_t)1U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = (uint64_t)0U,
            .v2 = (uint64_t)0U,
            .v1 = truncate_word(kk.v1, index),
            .v0 = kk.v0
          }
        );
    else if (word == (uint32_t)2U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = (uint64_t)0U,
            .v2 = truncate_word(kk.v2, index),
            .v1 = kk.v1,
            .v0 = kk.v0
          }
        );
    else
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = truncate_word(kk.v3, index),
            .v2 = kk.v2,
            .v1 = kk.v1,
            .v0 = kk.v0
          }
        );
    return ((Zeta_Steel_KeyUtils_raw_key){ .k = kk_, .significant_digits = w });
  }
}

static bool
__eq__Zeta_Steel_KeyUtils_u256(Zeta_Steel_KeyUtils_u256 y, Zeta_Steel_KeyUtils_u256 x)
{
  return true && x.v3 == y.v3 && x.v2 == y.v2 && x.v1 == y.v1 && x.v0 == y.v0;
}

static bool
__eq__Zeta_Steel_KeyUtils_raw_key(Zeta_Steel_KeyUtils_raw_key y, Zeta_Steel_KeyUtils_raw_key x)
{
  return
    true
    && __eq__Zeta_Steel_KeyUtils_u256(x.k, y.k)
    && x.significant_digits == y.significant_digits;
}

static bool
is_proper_descendent_(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return
    k0.significant_digits
    > k1.significant_digits
    && __eq__Zeta_Steel_KeyUtils_raw_key(truncate_key(k0, k1.significant_digits), k1);
}

static bool ith_bit_64(uint64_t x, uint32_t i)
{
  return (x >> i) % (uint64_t)2U == (uint64_t)1U;
}

static bool ith_bit(Zeta_Steel_KeyUtils_raw_key k0, uint16_t i)
{
  Zeta_Steel_KeyUtils_u256 kk = k0.k;
  __uint32_t_uint32_t scrut = bit_offset_in_word(i);
  uint32_t word = scrut.fst;
  uint32_t bit = scrut.snd;
  if (word == (uint32_t)0U)
    return ith_bit_64(kk.v0, bit);
  else if (word == (uint32_t)1U)
    return ith_bit_64(kk.v1, bit);
  else if (word == (uint32_t)2U)
    return ith_bit_64(kk.v2, bit);
  else
    return ith_bit_64(kk.v3, bit);
}

static bool desc_dir_raw(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return !ith_bit(k0, k1.significant_digits);
}

static bool eq_raw_key(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return eq_u256(k0.k, k1.k) && k0.significant_digits == k1.significant_digits;
}

static bool eq_base_key(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return eq_raw_key(k0, k1);
}

static bool is_root(Zeta_Steel_KeyUtils_raw_key r)
{
  return r.significant_digits == (uint16_t)0U;
}

static bool
is_proper_descendent(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return is_proper_descendent_(k0, k1);
}

static bool desc_dir(Zeta_Steel_KeyUtils_raw_key k0, Zeta_Steel_KeyUtils_raw_key k1)
{
  return desc_dir_raw(k0, k1);
}

static bool base_key_lt(Zeta_Steel_KeyUtils_raw_key bk1, Zeta_Steel_KeyUtils_raw_key bk2)
{
  if (bk1.significant_digits == bk2.significant_digits)
    if (bk1.k.v3 == bk2.k.v3)
      if (bk1.k.v2 == bk2.k.v2)
        if (bk1.k.v1 == bk2.k.v1)
          return bk1.k.v0 < bk2.k.v0;
        else
          return bk1.k.v1 < bk2.k.v1;
      else
        return bk1.k.v2 < bk2.k.v2;
    else
      return bk1.k.v3 < bk2.k.v3;
  else
    return bk1.significant_digits < bk2.significant_digits;
}

typedef uint32_t uninterpreted;

typedef struct timestamp_s
{
  uint32_t epoch;
  uint32_t counter;
}
timestamp;

static bool uu___is_ApplicationKey(Zeta_Steel_LogEntry_Types_key projectee)
{
  if (projectee.tag == Zeta_Steel_LogEntry_Types_ApplicationKey)
    return true;
  else
    return false;
}

typedef struct evictM_payload_s
{
  uint16_t s;
  uint16_t s_;
}
evictM_payload;

typedef struct evictB_payload_s
{
  uint16_t s1;
  timestamp t;
}
evictB_payload;

typedef struct evictBM_payload_s
{
  uint16_t s2;
  uint16_t s_1;
  timestamp t1;
}
evictBM_payload;

typedef struct runApp_payload_s
{
  uint8_t fid;
  uint32_t rest;
}
runApp_payload;

static bool uu___is_MValue(Zeta_Steel_LogEntry_Types_value projectee)
{
  if (projectee.tag == Zeta_Steel_LogEntry_Types_MValue)
    return true;
  else
    return false;
}

static bool uu___is_DValue(Zeta_Steel_LogEntry_Types_value projectee)
{
  if (projectee.tag == Zeta_Steel_LogEntry_Types_DValue)
    return true;
  else
    return false;
}

static bool is_value_of(Zeta_Steel_LogEntry_Types_key k, Zeta_Steel_LogEntry_Types_value v)
{
  if (uu___is_ApplicationKey(k))
    return uu___is_DValue(v);
  else
    return uu___is_MValue(v);
}

typedef struct record_s
{
  Zeta_Steel_LogEntry_Types_key fst;
  Zeta_Steel_LogEntry_Types_value snd;
}
record;

#define AddM 0
#define AddB 1
#define RunApp 2
#define EvictM 3
#define EvictB 4
#define EvictBM 5
#define NextEpoch 6
#define VerifyEpoch 7

typedef uint8_t log_entry_tags;

typedef struct log_entry_s
{
  log_entry_tags tag;
  union {
    struct
    {
      uint16_t s;
      uint16_t s_;
      record r;
    }
    case_AddM;
    struct
    {
      uint16_t s;
      timestamp ts;
      uint16_t tid;
      record r;
    }
    case_AddB;
    runApp_payload case_RunApp;
    evictM_payload case_EvictM;
    evictB_payload case_EvictB;
    evictBM_payload case_EvictBM;
  }
  ;
}
log_entry;

typedef struct stamped_record_s
{
  record record;
  timestamp timestamp;
  uint16_t thread_id;
}
stamped_record;

typedef struct __Zeta_Steel_LogEntry_Types_vbool_Zeta_Steel_LogEntry_Types_vbool_s
{
  Zeta_Steel_LogEntry_Types_vbool fst;
  Zeta_Steel_LogEntry_Types_vbool snd;
}
__Zeta_Steel_LogEntry_Types_vbool_Zeta_Steel_LogEntry_Types_vbool;

static bool eq_vbool(Zeta_Steel_LogEntry_Types_vbool v0, Zeta_Steel_LogEntry_Types_vbool v1)
{
  __Zeta_Steel_LogEntry_Types_vbool_Zeta_Steel_LogEntry_Types_vbool
  scrut = { .fst = v0, .snd = v1 };
  if
  (
    scrut.fst
    == Zeta_Steel_LogEntry_Types_Vfalse
    && scrut.snd == Zeta_Steel_LogEntry_Types_Vfalse
  )
    return true;
  else if
  (scrut.fst == Zeta_Steel_LogEntry_Types_Vtrue && scrut.snd == Zeta_Steel_LogEntry_Types_Vtrue)
    return true;
  else
    return false;
}

static bool
eq_descendent_hash_desc(
  Zeta_Steel_LogEntry_Types_descendent_hash_desc v0,
  Zeta_Steel_LogEntry_Types_descendent_hash_desc v1
)
{
  return
    eq_base_key(v0.dhd_key,
      v1.dhd_key)
    && eq_u256(v0.dhd_h, v1.dhd_h)
    && eq_vbool(v0.evicted_to_blum, v1.evicted_to_blum);
}

typedef struct
__Zeta_Steel_LogEntry_Types_descendent_hash_Zeta_Steel_LogEntry_Types_descendent_hash_s
{
  Zeta_Steel_LogEntry_Types_descendent_hash fst;
  Zeta_Steel_LogEntry_Types_descendent_hash snd;
}
__Zeta_Steel_LogEntry_Types_descendent_hash_Zeta_Steel_LogEntry_Types_descendent_hash;

static bool
eq_descendent_hash(
  Zeta_Steel_LogEntry_Types_descendent_hash v0,
  Zeta_Steel_LogEntry_Types_descendent_hash v1
)
{
  __Zeta_Steel_LogEntry_Types_descendent_hash_Zeta_Steel_LogEntry_Types_descendent_hash
  scrut = { .fst = v0, .snd = v1 };
  if
  (
    scrut.fst.tag
    == Zeta_Steel_LogEntry_Types_Dh_vnone
    && scrut.snd.tag == Zeta_Steel_LogEntry_Types_Dh_vnone
  )
    return true;
  else if
  (
    scrut.fst.tag
    == Zeta_Steel_LogEntry_Types_Dh_vsome
    && scrut.snd.tag == Zeta_Steel_LogEntry_Types_Dh_vsome
  )
  {
    Zeta_Steel_LogEntry_Types_descendent_hash_desc v11 = scrut.snd._0;
    Zeta_Steel_LogEntry_Types_descendent_hash_desc v01 = scrut.fst._0;
    return eq_descendent_hash_desc(v01, v11);
  }
  else
    return false;
}

static bool
eq_mval_value(Zeta_Steel_LogEntry_Types_mval_value v0, Zeta_Steel_LogEntry_Types_mval_value v1)
{
  return eq_descendent_hash(v0.l, v1.l) && eq_descendent_hash(v0.r, v1.r);
}

typedef struct __Zeta_Steel_LogEntry_Types_value_Zeta_Steel_LogEntry_Types_value_s
{
  Zeta_Steel_LogEntry_Types_value fst;
  Zeta_Steel_LogEntry_Types_value snd;
}
__Zeta_Steel_LogEntry_Types_value_Zeta_Steel_LogEntry_Types_value;

static bool eq_value(Zeta_Steel_LogEntry_Types_value v0, Zeta_Steel_LogEntry_Types_value v1)
{
  __Zeta_Steel_LogEntry_Types_value_Zeta_Steel_LogEntry_Types_value
  scrut = { .fst = v0, .snd = v1 };
  if
  (
    scrut.fst.tag
    == Zeta_Steel_LogEntry_Types_MValue
    && scrut.snd.tag == Zeta_Steel_LogEntry_Types_MValue
  )
  {
    Zeta_Steel_LogEntry_Types_mval_value mv1 = scrut.snd.case_MValue;
    Zeta_Steel_LogEntry_Types_mval_value mv0 = scrut.fst.case_MValue;
    return eq_mval_value(mv0, mv1);
  }
  else if
  (
    scrut.fst.tag
    == Zeta_Steel_LogEntry_Types_DValue
    &&
      scrut.fst.case_DValue.tag
      == FStar_Pervasives_Native_None
      &&
        scrut.snd.tag
        == Zeta_Steel_LogEntry_Types_DValue
        && scrut.snd.case_DValue.tag == FStar_Pervasives_Native_None
  )
    return true;
  else if
  (
    scrut.fst.tag
    == Zeta_Steel_LogEntry_Types_DValue
    &&
      scrut.fst.case_DValue.tag
      == FStar_Pervasives_Native_Some
      &&
        scrut.snd.tag
        == Zeta_Steel_LogEntry_Types_DValue
        && scrut.snd.case_DValue.tag == FStar_Pervasives_Native_Some
  )
  {
    Zeta_Steel_ApplicationTypes_value_type vt1 = scrut.snd.case_DValue.v;
    Zeta_Steel_ApplicationTypes_value_type vt0 = scrut.fst.case_DValue.v;
    return Zeta_Steel_ApplicationTypes_eq_value_type(vt0, vt1);
  }
  else
    return false;
}

typedef struct ha_s
{
  uint8_t *acc;
  uint32_t *ctr;
}
ha;

static ha create()
{
  uint8_t *p = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  uint8_t *res = p;
  uint8_t *acc = res;
  uint32_t *ctr = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
  return ((ha){ .acc = acc, .ctr = ctr });
}

static void aggregate_raw_hashes(uint8_t *b1, uint8_t *b2)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t *pt0 = b1;
    uint8_t x1 = pt0[i];
    uint8_t *pt1 = b2;
    uint8_t x2 = pt1[i];
    uint8_t *pt = b1;
    pt[i] = x1 ^ x2;
  }
}

static bool aggregate(ha b1, ha b2)
{
  uint32_t ctr1 = *b1.ctr;
  uint32_t ctr2 = *b2.ctr;
  uint64_t ctr = (uint64_t)ctr1 + (uint64_t)ctr2;
  if (ctr > (uint64_t)0xffffffffU)
    return false;
  else
  {
    aggregate_raw_hashes(b1.acc, b2.acc);
    *b1.ctr = (uint32_t)ctr;
    return true;
  }
}

static bool compare__uint8_t(uint8_t *a0, uint8_t *a1, uint32_t n)
{
  bool b = n == (uint32_t)0U;
  if (b)
    return true;
  else
  {
    uint32_t *r = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
    uint32_t i0 = *r;
    bool b10 = i0 == n;
    bool res0;
    if (b10)
      res0 = false;
    else
    {
      uint8_t *pt0 = a0;
      uint8_t elt0 = pt0[i0];
      uint8_t *pt = a1;
      uint8_t elt1 = pt[i0];
      res0 = elt0 == elt1;
    }
    bool cond = res0;
    while (cond)
    {
      uint32_t i = *r;
      *r = i + (uint32_t)1U;
      uint32_t i0 = *r;
      bool b1 = i0 == n;
      bool res;
      if (b1)
        res = false;
      else
      {
        uint8_t *pt0 = a0;
        uint8_t elt0 = pt0[i0];
        uint8_t *pt = a1;
        uint8_t elt1 = pt[i0];
        res = elt0 == elt1;
      }
      cond = res;
    }
    uint32_t i = *r;
    KRML_HOST_FREE(r);
    return i == n;
  }
}

static bool compare(ha b1, ha b2)
{
  uint32_t c1 = *b1.ctr;
  uint32_t c2 = *b2.ctr;
  if (c1 != c2)
    return false;
  else
  {
    bool b = compare__uint8_t(b1.acc, b2.acc, (uint32_t)32U);
    return b;
  }
}

static bool add(ha ha1, uint8_t *input, uint32_t l)
{
  uint32_t r = (uint32_t)1U;
  uint8_t *p10 = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  uint8_t *res = p10;
  uint8_t *acc = res;
  uint8_t *p11 = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint8_t));
  uint8_t *res0 = p11;
  uint8_t *_dummy = res0;
  Hacl_Blake2b_32_blake2b((uint32_t)32U, acc, l, input, (uint32_t)0U, _dummy);
  ha ha_ = { .acc = acc, .ctr = &r };
  bool v = aggregate(ha1, ha_);
  uint8_t *p1 = ha_.acc;
  KRML_HOST_FREE(p1);
  uint8_t *p12 = _dummy;
  KRML_HOST_FREE(p12);
  bool v0 = v;
  return v0;
}

typedef struct option__uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  uint32_t v;
}
option__uint32_t;

static option__uint32_t check_overflow_add32(uint32_t x, uint32_t y)
{
  if ((uint32_t)0xffffffffU - x < y)
    return ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  else
    return ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = x + y });
}

static option__uint32_t st_check_overflow_add32(uint32_t x, uint32_t y)
{
  option__uint32_t r = check_overflow_add32(x, y);
  return r;
}

#define MAdd 0
#define BAdd 1

typedef uint8_t add_method;

typedef struct option__uint16_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
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
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  __uint16_t_bool v;
}
option__uint16_t___bool;

typedef struct store_entry_s
{
  Zeta_Steel_LogEntry_Types_key key;
  Zeta_Steel_LogEntry_Types_value value;
  add_method add_method;
  option__uint16_t l_child_in_store;
  option__uint16_t r_child_in_store;
  option__uint16_t___bool parent_slot;
}
store_entry;

static bool check_slot_bounds(uint16_t s)
{
  return s < Zeta_Steel_ApplicationTypes_store_size;
}

static Zeta_Steel_LogEntry_Types_value init_value(Zeta_Steel_LogEntry_Types_key k)
{
  if (uu___is_ApplicationKey(k))
    return
      (
        (Zeta_Steel_LogEntry_Types_value){
          .tag = Zeta_Steel_LogEntry_Types_DValue,
          { .case_DValue = { .tag = FStar_Pervasives_Native_None } }
        }
      );
  else
    return
      (
        (Zeta_Steel_LogEntry_Types_value){
          .tag = Zeta_Steel_LogEntry_Types_MValue,
          {
            .case_MValue = {
              .l = { .tag = Zeta_Steel_LogEntry_Types_Dh_vnone },
              .r = { .tag = Zeta_Steel_LogEntry_Types_Dh_vnone }
            }
          }
        }
      );
}

static store_entry
mk_entry_full(
  Zeta_Steel_LogEntry_Types_key k,
  Zeta_Steel_LogEntry_Types_value v,
  add_method a,
  option__uint16_t l,
  option__uint16_t r,
  option__uint16_t___bool p
)
{
  return
    (
      (store_entry){
        .key = k,
        .value = v,
        .add_method = a,
        .l_child_in_store = l,
        .r_child_in_store = r,
        .parent_slot = p
      }
    );
}

static store_entry
mk_entry(Zeta_Steel_LogEntry_Types_key k, Zeta_Steel_LogEntry_Types_value v, add_method a)
{
  return
    mk_entry_full(k,
      v,
      a,
      ((option__uint16_t){ .tag = FStar_Pervasives_Native_None }),
      ((option__uint16_t){ .tag = FStar_Pervasives_Native_None }),
      ((option__uint16_t___bool){ .tag = FStar_Pervasives_Native_None }));
}

typedef struct option__Zeta_Steel_LogEntry_Types_mval_value_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_LogEntry_Types_mval_value v;
}
option__Zeta_Steel_LogEntry_Types_mval_value;

static option__Zeta_Steel_LogEntry_Types_mval_value
to_merkle_value(Zeta_Steel_LogEntry_Types_value v)
{
  if (v.tag == Zeta_Steel_LogEntry_Types_MValue)
  {
    Zeta_Steel_LogEntry_Types_mval_value v1 = v.case_MValue;
    return
      (
        (option__Zeta_Steel_LogEntry_Types_mval_value){
          .tag = FStar_Pervasives_Native_Some,
          .v = v1
        }
      );
  }
  else
    return ((option__Zeta_Steel_LogEntry_Types_mval_value){ .tag = FStar_Pervasives_Native_None });
}

static Zeta_Steel_LogEntry_Types_descendent_hash
desc_hash_dir(Zeta_Steel_LogEntry_Types_mval_value v, bool d)
{
  if (d)
    return v.l;
  else
    return v.r;
}

static Zeta_Steel_LogEntry_Types_mval_value
update_merkle_value(
  Zeta_Steel_LogEntry_Types_mval_value v,
  bool d,
  Zeta_Steel_KeyUtils_raw_key k,
  Zeta_Steel_KeyUtils_u256 h,
  bool b
)
{
  Zeta_Steel_LogEntry_Types_vbool ite;
  if (b)
    ite = Zeta_Steel_LogEntry_Types_Vtrue;
  else
    ite = Zeta_Steel_LogEntry_Types_Vfalse;
  Zeta_Steel_LogEntry_Types_descendent_hash
  desc_hash =
    {
      .tag = Zeta_Steel_LogEntry_Types_Dh_vsome,
      ._0 = { .dhd_key = k, .dhd_h = h, .evicted_to_blum = ite }
    };
  if (d)
    return ((Zeta_Steel_LogEntry_Types_mval_value){ .l = desc_hash, .r = v.r });
  else
    return ((Zeta_Steel_LogEntry_Types_mval_value){ .l = v.l, .r = desc_hash });
}

static store_entry update_parent_slot(store_entry r, __uint16_t_bool s)
{
  return
    (
      (store_entry){
        .key = r.key,
        .value = r.value,
        .add_method = r.add_method,
        .l_child_in_store = r.l_child_in_store,
        .r_child_in_store = r.r_child_in_store,
        .parent_slot = { .tag = FStar_Pervasives_Native_Some, .v = s }
      }
    );
}

static store_entry update_child(store_entry r, bool d, uint16_t s)
{
  if (d)
    return
      (
        (store_entry){
          .key = r.key,
          .value = r.value,
          .add_method = r.add_method,
          .l_child_in_store = { .tag = FStar_Pervasives_Native_Some, .v = s },
          .r_child_in_store = r.r_child_in_store,
          .parent_slot = r.parent_slot
        }
      );
  else
    return
      (
        (store_entry){
          .key = r.key,
          .value = r.value,
          .add_method = r.add_method,
          .l_child_in_store = r.l_child_in_store,
          .r_child_in_store = { .tag = FStar_Pervasives_Native_Some, .v = s },
          .parent_slot = r.parent_slot
        }
      );
}

static option__uint16_t child_slot(store_entry r, bool d)
{
  if (d)
    return r.l_child_in_store;
  else
    return r.r_child_in_store;
}

static bool timestamp_lt(timestamp t0, timestamp t1)
{
  return t0.epoch < t1.epoch || t0.epoch == t1.epoch && t0.counter < t1.counter;
}

typedef struct timestamp_key_s
{
  timestamp fst;
  Zeta_Steel_KeyUtils_raw_key snd;
}
timestamp_key;

static bool __eq__Zeta_Steel_LogEntry_Types_timestamp(timestamp y, timestamp x)
{
  return true && x.epoch == y.epoch && x.counter == y.counter;
}

static bool tk_lt(timestamp_key tk1, timestamp_key tk2)
{
  timestamp t1 = tk1.fst;
  Zeta_Steel_KeyUtils_raw_key k1 = tk1.snd;
  timestamp t2 = tk2.fst;
  Zeta_Steel_KeyUtils_raw_key k2 = tk2.snd;
  return
    timestamp_lt(t1,
      t2)
    || __eq__Zeta_Steel_LogEntry_Types_timestamp(t1, t2) && base_key_lt(k1, k2);
}

static timestamp max(timestamp t0, timestamp t1)
{
  if (timestamp_lt(t0, t1))
    return t1;
  else
    return t0;
}

static uint32_t epoch_of_timestamp(timestamp t)
{
  return t.epoch;
}

static bool is_root_key(Zeta_Steel_LogEntry_Types_key k)
{
  if (k.tag == Zeta_Steel_LogEntry_Types_InternalKey)
  {
    Zeta_Steel_KeyUtils_raw_key k1 = k.case_InternalKey;
    return is_root(k1);
  }
  else
    return false;
}

static bool epoch_greater_than_last_verified_epoch(option__uint32_t lve, uint32_t e)
{
  if (lve.tag == FStar_Pervasives_Native_None)
    return true;
  else if (lve.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e_ = lve.v;
    return e_ < e;
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

static option__uint32_t maybe_increment_last_verified_epoch(option__uint32_t e)
{
  if (e.tag == FStar_Pervasives_Native_None)
    return ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = (uint32_t)0U });
  else if (e.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e1 = e.v;
    return check_overflow_add32(e1, (uint32_t)1U);
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

static bool above_high_water_mark(option__uint32_t h, uint32_t e)
{
  if (h.tag == FStar_Pervasives_Native_None)
    return true;
  else if (h.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e0 = h.v;
    return e0 < e;
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
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  __uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t v;
}
option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t
*dtuple2___FStar_Pervasives_Native_option_K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t____;

typedef struct tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  uint32_t store_len;
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *store;
}
tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct all_epoch_hashes_s
{
  tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t etbl;
  option__uint32_t *high;
}
all_epoch_hashes;

typedef bool *dtuple2___bool____;

typedef struct __uint32_t_Prims_dtuple2__bool_____s
{
  uint32_t fst;
  bool *snd;
}
__uint32_t_Prims_dtuple2__bool____;

typedef struct option__K___uint32_t_Prims_dtuple2__bool_____s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  __uint32_t_Prims_dtuple2__bool____ v;
}
option__K___uint32_t_Prims_dtuple2__bool____;

typedef option__K___uint32_t_Prims_dtuple2__bool____
*dtuple2___FStar_Pervasives_Native_option_K___uint32_t_Prims_dtuple2__bool________;

typedef struct tbl__uint32_t_Prims_dtuple2__bool_____s
{
  uint32_t store_len;
  option__K___uint32_t_Prims_dtuple2__bool____ *store;
}
tbl__uint32_t_Prims_dtuple2__bool____;

typedef struct epoch_tid_bitmaps_s
{
  tbl__uint32_t_Prims_dtuple2__bool____ etbl;
  option__uint32_t *high;
}
epoch_tid_bitmaps;

typedef struct aggregate_epoch_hashes_s
{
  all_epoch_hashes hashes;
  epoch_tid_bitmaps tid_bitmaps;
  option__uint32_t *max_certified_epoch;
  cancellable_lock lock;
}
aggregate_epoch_hashes;

static uint32_t all_hashes_size = (uint32_t)32U;

static uint32_t tid_bitmaps_size = (uint32_t)32U;

static all_epoch_hashes create__Zeta_Steel_EpochHashes_epoch_hashes_t(uint32_t n)
{
  KRML_CHECK_SIZE(sizeof (option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t), n);
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t
  *p = KRML_HOST_MALLOC(sizeof (option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t) * n);
  for (uint32_t _i = 0U; _i < n; ++_i)
    p[_i]
    =
      (
        (option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *res = p;
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *store = res;
  tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t etbl = { .store_len = n, .store = store };
  KRML_CHECK_SIZE(sizeof (option__uint32_t), (uint32_t)1U);
  option__uint32_t *high = KRML_HOST_MALLOC(sizeof (option__uint32_t));
  high[0U] = ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  return ((all_epoch_hashes){ .etbl = etbl, .high = high });
}

static epoch_tid_bitmaps create__Prims_dtuple2__bool____(uint32_t n)
{
  KRML_CHECK_SIZE(sizeof (option__K___uint32_t_Prims_dtuple2__bool____), n);
  option__K___uint32_t_Prims_dtuple2__bool____
  *p = KRML_HOST_MALLOC(sizeof (option__K___uint32_t_Prims_dtuple2__bool____) * n);
  for (uint32_t _i = 0U; _i < n; ++_i)
    p[_i]
    = ((option__K___uint32_t_Prims_dtuple2__bool____){ .tag = FStar_Pervasives_Native_None });
  option__K___uint32_t_Prims_dtuple2__bool____ *res = p;
  option__K___uint32_t_Prims_dtuple2__bool____ *store = res;
  tbl__uint32_t_Prims_dtuple2__bool____ etbl = { .store_len = n, .store = store };
  KRML_CHECK_SIZE(sizeof (option__uint32_t), (uint32_t)1U);
  option__uint32_t *high = KRML_HOST_MALLOC(sizeof (option__uint32_t));
  high[0U] = ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  return ((epoch_tid_bitmaps){ .etbl = etbl, .high = high });
}

static aggregate_epoch_hashes create0()
{
  all_epoch_hashes hashes = create__Zeta_Steel_EpochHashes_epoch_hashes_t(all_hashes_size);
  epoch_tid_bitmaps tid_bitmaps = create__Prims_dtuple2__bool____(tid_bitmaps_size);
  KRML_CHECK_SIZE(sizeof (option__uint32_t), (uint32_t)1U);
  option__uint32_t *max_certified_epoch = KRML_HOST_MALLOC(sizeof (option__uint32_t));
  max_certified_epoch[0U] = ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  cancellable_lock lock = new_cancellable_lock();
  return
    (
      (aggregate_epoch_hashes){
        .hashes = hashes,
        .tid_bitmaps = tid_bitmaps,
        .max_certified_epoch = max_certified_epoch,
        .lock = lock
      }
    );
}

static bool check_all_ones(bool *a)
{
  bool b = Zeta_Steel_ApplicationTypes_n_threads == (uint32_t)0U;
  if (b)
    return true;
  else
  {
    uint32_t *r = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
    uint32_t i0 = *r;
    bool b10 = i0 == Zeta_Steel_ApplicationTypes_n_threads;
    bool res0;
    if (b10)
      res0 = false;
    else
    {
      bool *pt = a;
      res0 = pt[i0];
    }
    bool cond = res0;
    while (cond)
    {
      uint32_t i = *r;
      *r = i + (uint32_t)1U;
      uint32_t i0 = *r;
      bool b1 = i0 == Zeta_Steel_ApplicationTypes_n_threads;
      bool res;
      if (b1)
        res = false;
      else
      {
        bool *pt = a;
        res = pt[i0];
      }
      cond = res;
    }
    uint32_t i = *r;
    KRML_HOST_FREE(r);
    return i == Zeta_Steel_ApplicationTypes_n_threads;
  }
}

#define Found 0
#define Fresh 1
#define NotFound 2

typedef uint8_t get_result__Prims_dtuple2___bool_____tags;

typedef struct get_result__Prims_dtuple2___bool_____s
{
  get_result__Prims_dtuple2___bool_____tags tag;
  dtuple2___bool____ _0;
}
get_result__Prims_dtuple2___bool____;

#define Present 0
#define Absent 1
#define Missing 2

typedef uint8_t get_result__uint32_t_Prims_dtuple2___bool_____tags;

typedef struct get_result__uint32_t_Prims_dtuple2___bool_____s
{
  get_result__uint32_t_Prims_dtuple2___bool_____tags tag;
  union {
    bool *case_Present;
    uint32_t case_Missing;
  }
  ;
}
get_result__uint32_t_Prims_dtuple2___bool____;

static get_result__Prims_dtuple2___bool____
get__Prims_dtuple2__bool____(epoch_tid_bitmaps a, uint32_t i)
{
  option__uint32_t high_value = *a.high;
  bool r = above_high_water_mark(high_value, i);
  if (r)
    return ((get_result__Prims_dtuple2___bool____){ .tag = Fresh });
  else
  {
    uint32_t idx = i % a.etbl.store_len;
    option__K___uint32_t_Prims_dtuple2__bool____ *pt = a.etbl.store;
    option__K___uint32_t_Prims_dtuple2__bool____ vopt = pt[idx];
    get_result__uint32_t_Prims_dtuple2___bool____ r1;
    if (vopt.tag == FStar_Pervasives_Native_None)
      r1 = ((get_result__uint32_t_Prims_dtuple2___bool____){ .tag = Absent });
    else if (vopt.tag == FStar_Pervasives_Native_Some)
    {
      bool *x = vopt.v.snd;
      uint32_t i_ = vopt.v.fst;
      if (i != i_)
        r1 =
          (
            (get_result__uint32_t_Prims_dtuple2___bool____){
              .tag = Missing,
              { .case_Missing = i_ }
            }
          );
      else
        r1 =
          ((get_result__uint32_t_Prims_dtuple2___bool____){ .tag = Present, { .case_Present = x } });
    }
    else
      r1 =
        KRML_EABORT(get_result__uint32_t_Prims_dtuple2___bool____,
          "unreachable (pattern matches are exhaustive in F*)");
    get_result__uint32_t_Prims_dtuple2___bool____ x = r1;
    if (x.tag == Missing)
      return ((get_result__Prims_dtuple2___bool____){ .tag = NotFound });
    else if (x.tag == Absent)
      return ((get_result__Prims_dtuple2___bool____){ .tag = NotFound });
    else if (x.tag == Present)
    {
      bool *x1 = x.case_Present;
      return ((get_result__Prims_dtuple2___bool____){ .tag = Found, ._0 = x1 });
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
}

static bool check_bitmap_for_epoch(epoch_tid_bitmaps tid_bitmaps, uint32_t e)
{
  get_result__Prims_dtuple2___bool____ res = get__Prims_dtuple2__bool____(tid_bitmaps, e);
  if (res.tag == Found)
  {
    bool *a = res._0;
    bool b = check_all_ones(a);
    return b;
  }
  else
    return false;
}

typedef struct get_result__Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  get_result__Prims_dtuple2___bool_____tags tag;
  epoch_hashes_t _0;
}
get_result__Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  get_result__uint32_t_Prims_dtuple2___bool_____tags tag;
  union {
    epoch_hashes_t case_Present;
    uint32_t case_Missing;
  }
  ;
}
get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

static get_result__Zeta_Steel_EpochHashes_epoch_hashes_t
get__Zeta_Steel_EpochHashes_epoch_hashes_t(all_epoch_hashes a, uint32_t i)
{
  option__uint32_t high_value = *a.high;
  bool r = above_high_water_mark(high_value, i);
  if (r)
    return ((get_result__Zeta_Steel_EpochHashes_epoch_hashes_t){ .tag = Fresh });
  else
  {
    uint32_t idx = i % a.etbl.store_len;
    option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *pt = a.etbl.store;
    option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t vopt = pt[idx];
    get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t r1;
    if (vopt.tag == FStar_Pervasives_Native_None)
      r1 = ((get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t){ .tag = Absent });
    else if (vopt.tag == FStar_Pervasives_Native_Some)
    {
      epoch_hashes_t x = vopt.v.snd;
      uint32_t i_ = vopt.v.fst;
      if (i != i_)
        r1 =
          (
            (get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t){
              .tag = Missing,
              { .case_Missing = i_ }
            }
          );
      else
        r1 =
          (
            (get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t){
              .tag = Present,
              { .case_Present = x }
            }
          );
    }
    else
      r1 =
        KRML_EABORT(get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t,
          "unreachable (pattern matches are exhaustive in F*)");
    get_result__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t x = r1;
    if (x.tag == Missing)
      return ((get_result__Zeta_Steel_EpochHashes_epoch_hashes_t){ .tag = NotFound });
    else if (x.tag == Absent)
      return ((get_result__Zeta_Steel_EpochHashes_epoch_hashes_t){ .tag = NotFound });
    else if (x.tag == Present)
    {
      epoch_hashes_t x1 = x.case_Present;
      return ((get_result__Zeta_Steel_EpochHashes_epoch_hashes_t){ .tag = Found, ._0 = x1 });
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
}

static bool check_hash_equality_for_epoch(all_epoch_hashes hashes, uint32_t e)
{
  get_result__Zeta_Steel_EpochHashes_epoch_hashes_t
  res = get__Zeta_Steel_EpochHashes_epoch_hashes_t(hashes, e);
  if (res.tag == Found)
  {
    epoch_hashes_t ehs = res._0;
    bool b = compare(ehs.hadd, ehs.hevict);
    return b;
  }
  else
    return false;
}

static bool
try_increment_max(all_epoch_hashes hashes, epoch_tid_bitmaps bitmaps, option__uint32_t *max)
{
  option__uint32_t e = *max;
  option__uint32_t v;
  if (e.tag == FStar_Pervasives_Native_None)
    v = ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = (uint32_t)0U });
  else if (e.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e1 = e.v;
    v = check_overflow_add32(e1, (uint32_t)1U);
  }
  else
    v = KRML_EABORT(option__uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  if (v.tag == FStar_Pervasives_Native_None)
    return false;
  else if (v.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e_ = v.v;
    bool ready = check_bitmap_for_epoch(bitmaps, e_);
    if (!ready)
      return false;
    else
    {
      bool b = check_hash_equality_for_epoch(hashes, e_);
      if (!b)
        return false;
      else
      {
        *max = ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = e_ });
        return true;
      }
    }
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

static option__uint32_t
try_advance_max(all_epoch_hashes hashes, epoch_tid_bitmaps bitmaps, option__uint32_t *max)
{
  bool r = true;
  while (r)
  {
    bool b = try_increment_max(hashes, bitmaps, max);
    r = b;
  }
  return *max;
}

static void release_lock(cancellable_lock lock)
{
  release0(lock);
}

static Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
advance_and_read_max_certified_epoch(aggregate_epoch_hashes aeh)
{
  bool b = acquire0(aeh.lock);
  bool b1 = !b;
  if (b1)
    return
      (
        (Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result){
          .tag = Zeta_Steel_AggregateEpochHashes_Read_max_error
        }
      );
  else
  {
    option__uint32_t max = try_advance_max(aeh.hashes, aeh.tid_bitmaps, aeh.max_certified_epoch);
    if (max.tag == FStar_Pervasives_Native_None)
    {
      Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
      r = { .tag = Zeta_Steel_AggregateEpochHashes_Read_max_none };
      release_lock(aeh.lock);
      return r;
    }
    else if (max.tag == FStar_Pervasives_Native_Some)
    {
      uint32_t max_v = max.v;
      release_lock(aeh.lock);
      return
        (
          (Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result){
            .tag = Zeta_Steel_AggregateEpochHashes_Read_max_some,
            ._0 = max_v
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
}

typedef struct __Zeta_Steel_LogEntry_Types_log_entry_uint32_t_s
{
  log_entry fst;
  uint32_t snd;
}
__Zeta_Steel_LogEntry_Types_log_entry_uint32_t;

typedef struct option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  __Zeta_Steel_LogEntry_Types_log_entry_uint32_t v;
}
option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t;

extern option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t
zeta__parser_log_entry(uint32_t x0, uint32_t x1, uint32_t x2, uint8_t *x3);

extern uint32_t
zeta__serialize_stamped_record(uint32_t x0, uint32_t x1, uint8_t *x2, stamped_record x3);

extern uint32_t
zeta__serialize_value(
  uint32_t x0,
  uint32_t x1,
  uint8_t *x2,
  Zeta_Steel_LogEntry_Types_value x3
);

typedef struct __Zeta_Steel_KeyUtils_u256_uint32_t_s
{
  Zeta_Steel_KeyUtils_u256 fst;
  uint32_t snd;
}
__Zeta_Steel_KeyUtils_u256_uint32_t;

typedef struct option__Zeta_Steel_KeyUtils_u256___uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  __Zeta_Steel_KeyUtils_u256_uint32_t v;
}
option__Zeta_Steel_KeyUtils_u256___uint32_t;

extern option__Zeta_Steel_KeyUtils_u256___uint32_t
zeta__parser_u256(uint32_t x0, uint32_t x1, uint32_t x2, uint8_t *x3);

typedef struct hasher_t_s
{
  uint8_t *serialization_buffer;
  uint8_t *hash_buffer;
  uint8_t *dummy;
}
hasher_t;

static hasher_t alloc()
{
  uint8_t *p0 = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  uint8_t *res = p0;
  uint8_t *hb = res;
  uint8_t *p1 = KRML_HOST_CALLOC((uint32_t)4096U, sizeof (uint8_t));
  uint8_t *res0 = p1;
  uint8_t *sb = res0;
  uint8_t *p = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint8_t));
  uint8_t *res1 = p;
  uint8_t *dummy = res1;
  return ((hasher_t){ .serialization_buffer = sb, .hash_buffer = hb, .dummy = dummy });
}

static Zeta_Steel_KeyUtils_u256 read_hash_u256(uint8_t *hb)
{
  option__Zeta_Steel_KeyUtils_u256___uint32_t
  res = zeta__parser_u256((uint32_t)32U, (uint32_t)0U, (uint32_t)32U, hb);
  if (res.tag == FStar_Pervasives_Native_Some)
    return res.v.fst;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Zeta_Steel_KeyUtils_u256 hash_value(hasher_t h, Zeta_Steel_LogEntry_Types_value v)
{
  uint32_t n = zeta__serialize_value((uint32_t)4096U, (uint32_t)0U, h.serialization_buffer, v);
  Hacl_Blake2b_32_blake2b((uint32_t)32U,
    h.hash_buffer,
    n,
    h.serialization_buffer,
    (uint32_t)0U,
    h.dummy);
  Zeta_Steel_KeyUtils_u256 res = read_hash_u256(h.hash_buffer);
  return res;
}

typedef struct option__Zeta_Steel_ThreadStateModel_store_entry_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
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
  option__uint32_t *last_verified_epoch;
  uint8_t *serialization_buffer;
  hasher_t hasher;
}
Zeta_Steel_VerifierTypes_thread_state_t;

static uint32_t as_u32(uint16_t s)
{
  return (uint32_t)s;
}

#define Run_app_parsing_failure 0
#define Run_app_verify_failure 1
#define Run_app_success 2

typedef uint8_t verify_runapp_result_tags;

typedef struct verify_runapp_result_s
{
  verify_runapp_result_tags tag;
  uint32_t wrote;
}
verify_runapp_result;

extern verify_runapp_result
Zeta_Steel_Application_run_app_function(
  uint32_t log_len,
  runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  Zeta_Steel_VerifierTypes_thread_state_t t
);

extern Zeta_Steel_KeyUtils_raw_key
Zeta_Steel_Application_key_type_to_base_key(Zeta_Steel_ApplicationTypes_key_type k);

extern uint32_t zeta__runapp_payload_offset(log_entry e);

static uint32_t as_u320(uint16_t s)
{
  return (uint32_t)s;
}

static void fail(Zeta_Steel_VerifierTypes_thread_state_t t)
{
  *t.failed = true;
}

static bool fail_as(Zeta_Steel_VerifierTypes_thread_state_t t)
{
  *t.failed = true;
  return true;
}

static Zeta_Steel_KeyUtils_raw_key to_base_key(Zeta_Steel_LogEntry_Types_key x)
{
  if (x.tag == Zeta_Steel_LogEntry_Types_InternalKey)
    return x.case_InternalKey;
  else if (x.tag == Zeta_Steel_LogEntry_Types_ApplicationKey)
  {
    Zeta_Steel_ApplicationTypes_key_type k = x.case_ApplicationKey;
    Zeta_Steel_KeyUtils_raw_key k_ = Zeta_Steel_Application_key_type_to_base_key(k);
    return k_;
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

static bool check_failed(Zeta_Steel_VerifierTypes_thread_state_t t)
{
  return *t.failed;
}

static void
madd_to_store_split(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  Zeta_Steel_LogEntry_Types_key k,
  Zeta_Steel_LogEntry_Types_value v,
  uint16_t s_,
  bool d,
  bool d2
)
{
  bool b = is_value_of(k, v);
  if (!b)
    fail(t);
  else
  {
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s)];
    option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
    option__Zeta_Steel_ThreadStateModel_store_entry *pt1 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res1 = pt1[as_u320(s_)];
    option__Zeta_Steel_ThreadStateModel_store_entry res2 = res1;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt_ = res2;
    if (ropt.tag == FStar_Pervasives_Native_Some)
      fail(t);
    else if (ropt_.tag == FStar_Pervasives_Native_None)
      fail(t);
    else if (ropt_.tag == FStar_Pervasives_Native_Some)
    {
      store_entry r_ = ropt_.v;
      __uint16_t_bool p = { .fst = s_, .snd = d };
      option__uint16_t s2_opt = child_slot(r_, d);
      if (s2_opt.tag == FStar_Pervasives_Native_None)
        fail(t);
      else if (s2_opt.tag == FStar_Pervasives_Native_Some)
      {
        uint16_t s2 = s2_opt.v;
        option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
        option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s2)];
        option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
        option__Zeta_Steel_ThreadStateModel_store_entry r2opt = res0;
        if (r2opt.tag == FStar_Pervasives_Native_None)
          fail(t);
        else if (r2opt.tag == FStar_Pervasives_Native_Some)
        {
          store_entry r2 = r2opt.v;
          store_entry
          e =
            mk_entry_full(k,
              v,
              MAdd,
              ((option__uint16_t){ .tag = FStar_Pervasives_Native_None }),
              ((option__uint16_t){ .tag = FStar_Pervasives_Native_None }),
              ((option__uint16_t___bool){ .tag = FStar_Pervasives_Native_Some, .v = p }));
          store_entry e1 = update_child(e, d2, s2);
          store_entry e_ = update_child(r_, d, s);
          __uint16_t_bool p2new = { .fst = s, .snd = d2 };
          store_entry e2 = update_parent_slot(r2, p2new);
          option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
          pt[as_u320(s)] =
            (
              (option__Zeta_Steel_ThreadStateModel_store_entry){
                .tag = FStar_Pervasives_Native_Some,
                .v = e1
              }
            );
          option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
          pt0[as_u320(s_)] =
            (
              (option__Zeta_Steel_ThreadStateModel_store_entry){
                .tag = FStar_Pervasives_Native_Some,
                .v = e_
              }
            );
          option__Zeta_Steel_ThreadStateModel_store_entry *pt1 = t.store;
          pt1[as_u320(s2)] =
            (
              (option__Zeta_Steel_ThreadStateModel_store_entry){
                .tag = FStar_Pervasives_Native_Some,
                .v = e2
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
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
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
}

static void
madd_to_store(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  Zeta_Steel_LogEntry_Types_key k,
  Zeta_Steel_LogEntry_Types_value v,
  uint16_t s_,
  bool d
)
{
  bool b = is_value_of(k, v);
  if (!b)
    fail(t);
  else
  {
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s)];
    option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
    option__Zeta_Steel_ThreadStateModel_store_entry *pt1 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res1 = pt1[as_u320(s_)];
    option__Zeta_Steel_ThreadStateModel_store_entry res2 = res1;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt_ = res2;
    if (ropt.tag == FStar_Pervasives_Native_Some)
      fail(t);
    else if (ropt_.tag == FStar_Pervasives_Native_None)
      fail(t);
    else if (ropt_.tag == FStar_Pervasives_Native_Some)
    {
      store_entry r_ = ropt_.v;
      store_entry
      new_entry =
        {
          .key = k, .value = v, .add_method = MAdd,
          .l_child_in_store = { .tag = FStar_Pervasives_Native_None },
          .r_child_in_store = { .tag = FStar_Pervasives_Native_None },
          .parent_slot = { .tag = FStar_Pervasives_Native_Some, .v = { .fst = s_, .snd = d } }
        };
      option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
      pt0[as_u320(s)] =
        (
          (option__Zeta_Steel_ThreadStateModel_store_entry){
            .tag = FStar_Pervasives_Native_Some,
            .v = new_entry
          }
        );
      store_entry r_1;
      if (d)
        r_1 =
          (
            (store_entry){
              .key = r_.key,
              .value = r_.value,
              .add_method = r_.add_method,
              .l_child_in_store = { .tag = FStar_Pervasives_Native_Some, .v = s },
              .r_child_in_store = r_.r_child_in_store,
              .parent_slot = r_.parent_slot
            }
          );
      else
        r_1 =
          (
            (store_entry){
              .key = r_.key,
              .value = r_.value,
              .add_method = r_.add_method,
              .l_child_in_store = r_.l_child_in_store,
              .r_child_in_store = { .tag = FStar_Pervasives_Native_Some, .v = s },
              .parent_slot = r_.parent_slot
            }
          );
      option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
      pt[as_u320(s_)] =
        (
          (option__Zeta_Steel_ThreadStateModel_store_entry){
            .tag = FStar_Pervasives_Native_Some,
            .v = r_1
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
}

static bool uu___is_Some__uint16_t(option__uint16_t projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

static bool entry_points_to_some_slot(store_entry r, bool d)
{
  if (d)
    return uu___is_Some__uint16_t(r.l_child_in_store);
  else
    return uu___is_Some__uint16_t(r.r_child_in_store);
}

static void
update_value(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  Zeta_Steel_LogEntry_Types_value r
)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  if (res0.tag == FStar_Pervasives_Native_Some)
  {
    store_entry v = res0.v;
    option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
    pt[as_u320(s)] =
      (
        (option__Zeta_Steel_ThreadStateModel_store_entry){
          .tag = FStar_Pervasives_Native_Some,
          .v = {
            .key = v.key, .value = r, .add_method = v.add_method,
            .l_child_in_store = v.l_child_in_store, .r_child_in_store = v.r_child_in_store,
            .parent_slot = v.parent_slot
          }
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
vaddm_core(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_, record r)
{
  bool b = !check_slot_bounds(s) || !check_slot_bounds(s_);
  if (b)
  {
    fail(t);
    return true;
  }
  else
  {
    Zeta_Steel_LogEntry_Types_key gk = r.fst;
    Zeta_Steel_LogEntry_Types_value gv = r.snd;
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s_)];
    option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
    if (ropt.tag == FStar_Pervasives_Native_None)
    {
      fail(t);
      return true;
    }
    else if (ropt.tag == FStar_Pervasives_Native_Some)
    {
      store_entry r_ = ropt.v;
      Zeta_Steel_KeyUtils_raw_key k_ = to_base_key(r_.key);
      Zeta_Steel_LogEntry_Types_value v_ = r_.value;
      Zeta_Steel_KeyUtils_raw_key k = to_base_key(gk);
      if (!is_proper_descendent(k, k_))
      {
        fail(t);
        return true;
      }
      else
      {
        option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
        option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
        option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
        option__Zeta_Steel_ThreadStateModel_store_entry sopt = res0;
        if (sopt.tag == FStar_Pervasives_Native_Some)
        {
          fail(t);
          return true;
        }
        else
        {
          option__Zeta_Steel_LogEntry_Types_mval_value scrut0 = to_merkle_value(v_);
          if (scrut0.tag == FStar_Pervasives_Native_None)
          {
            fail(t);
            return true;
          }
          else if (scrut0.tag == FStar_Pervasives_Native_Some)
          {
            Zeta_Steel_LogEntry_Types_mval_value v_1 = scrut0.v;
            bool d = desc_dir(k, k_);
            Zeta_Steel_LogEntry_Types_descendent_hash dh_ = desc_hash_dir(v_1, d);
            Zeta_Steel_KeyUtils_u256 h = hash_value(t.hasher, gv);
            if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vnone)
              if (!eq_value(gv, init_value(gk)))
              {
                bool b1 = fail_as(t);
                return b1;
              }
              else if (entry_points_to_some_slot(r_, d))
              {
                bool b1 = fail_as(t);
                return b1;
              }
              else
              {
                madd_to_store(t, s, gk, gv, s_, d);
                Zeta_Steel_LogEntry_Types_mval_value
                v__upd =
                  update_merkle_value(v_1,
                    d,
                    k,
                    (
                      (Zeta_Steel_KeyUtils_u256){
                        .v3 = (uint64_t)0U,
                        .v2 = (uint64_t)0U,
                        .v1 = (uint64_t)0U,
                        .v0 = (uint64_t)0U
                      }
                    ),
                    false);
                update_value(t,
                  s_,
                  (
                    (Zeta_Steel_LogEntry_Types_value){
                      .tag = Zeta_Steel_LogEntry_Types_MValue,
                      { .case_MValue = v__upd }
                    }
                  ));
                return true;
              }
            else if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vsome)
            {
              Zeta_Steel_LogEntry_Types_vbool b2 = dh_._0.evicted_to_blum;
              Zeta_Steel_KeyUtils_u256 h2 = dh_._0.dhd_h;
              Zeta_Steel_KeyUtils_raw_key k2 = dh_._0.dhd_key;
              if (eq_base_key(k2, k))
                if (!(eq_u256(h2, h) && b2 == Zeta_Steel_LogEntry_Types_Vfalse))
                {
                  bool b1 = fail_as(t);
                  return b1;
                }
                else if (entry_points_to_some_slot(r_, d))
                {
                  bool b1 = fail_as(t);
                  return b1;
                }
                else
                {
                  madd_to_store(t, s, gk, gv, s_, d);
                  return true;
                }
              else if (!eq_value(gv, init_value(gk)))
              {
                bool b1 = fail_as(t);
                return b1;
              }
              else if (!is_proper_descendent(k2, k))
              {
                bool b1 = fail_as(t);
                return b1;
              }
              else
              {
                bool d2 = desc_dir(k2, k);
                option__Zeta_Steel_LogEntry_Types_mval_value scrut = to_merkle_value(gv);
                if (scrut.tag == FStar_Pervasives_Native_Some)
                {
                  Zeta_Steel_LogEntry_Types_mval_value mv = scrut.v;
                  Zeta_Steel_LogEntry_Types_mval_value
                  mv_upd =
                    update_merkle_value(mv,
                      d2,
                      k2,
                      h2,
                      b2 == Zeta_Steel_LogEntry_Types_Vtrue);
                  Zeta_Steel_LogEntry_Types_mval_value
                  v__upd =
                    update_merkle_value(v_1,
                      d,
                      k,
                      (
                        (Zeta_Steel_KeyUtils_u256){
                          .v3 = (uint64_t)0U,
                          .v2 = (uint64_t)0U,
                          .v1 = (uint64_t)0U,
                          .v0 = (uint64_t)0U
                        }
                      ),
                      false);
                  bool b1 = entry_points_to_some_slot(r_, d);
                  if (b1)
                  {
                    madd_to_store_split(t,
                      s,
                      gk,
                      (
                        (Zeta_Steel_LogEntry_Types_value){
                          .tag = Zeta_Steel_LogEntry_Types_MValue,
                          { .case_MValue = mv_upd }
                        }
                      ),
                      s_,
                      d,
                      d2);
                    update_value(t,
                      s_,
                      (
                        (Zeta_Steel_LogEntry_Types_value){
                          .tag = Zeta_Steel_LogEntry_Types_MValue,
                          { .case_MValue = v__upd }
                        }
                      ));
                    return true;
                  }
                  else
                  {
                    madd_to_store(t,
                      s,
                      gk,
                      (
                        (Zeta_Steel_LogEntry_Types_value){
                          .tag = Zeta_Steel_LogEntry_Types_MValue,
                          { .case_MValue = mv_upd }
                        }
                      ),
                      s_,
                      d);
                    update_value(t,
                      s_,
                      (
                        (Zeta_Steel_LogEntry_Types_value){
                          .tag = Zeta_Steel_LogEntry_Types_MValue,
                          { .case_MValue = v__upd }
                        }
                      ));
                    return true;
                  }
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
          {
            KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
              __FILE__,
              __LINE__,
              "unreachable (pattern matches are exhaustive in F*)");
            KRML_HOST_EXIT(255U);
          }
        }
      }
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
}

static bool vaddm(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_, record r)
{
  bool b = vaddm_core(t, s, s_, r);
  return b;
}

typedef struct option__Zeta_Steel_LogEntry_Types_timestamp_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  timestamp v;
}
option__Zeta_Steel_LogEntry_Types_timestamp;

static option__Zeta_Steel_LogEntry_Types_timestamp next(timestamp t)
{
  option__uint32_t scrut = check_overflow_add32(t.counter, (uint32_t)1U);
  if (scrut.tag == FStar_Pervasives_Native_None)
    return ((option__Zeta_Steel_LogEntry_Types_timestamp){ .tag = FStar_Pervasives_Native_None });
  else if (scrut.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t ctr = scrut.v;
    return
      (
        (option__Zeta_Steel_LogEntry_Types_timestamp){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .epoch = t.epoch, .counter = ctr }
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

#define HAdd 0
#define HEvict 1

typedef uint8_t htype;

static bool ha_add(ha ha0, uint32_t l, uint8_t *input)
{
  bool x = add(ha0, input, l);
  return x;
}

static epoch_hashes_t new_epoch(uint32_t e)
{
  ha hadd = create();
  ha hev = create();
  return ((epoch_hashes_t){ .hadd = hadd, .hevict = hev });
}

static void
put__Zeta_Steel_EpochHashes_epoch_hashes_t(all_epoch_hashes a, uint32_t i, epoch_hashes_t x)
{
  uint32_t idx = i % a.etbl.store_len;
  option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *pt = a.etbl.store;
  pt[idx] =
    (
      (option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t){
        .tag = FStar_Pervasives_Native_Some,
        .v = { .fst = i, .snd = x }
      }
    );
  option__uint32_t high = *a.high;
  bool r = above_high_water_mark(high, i);
  if (r)
    *a.high = ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = i });
}

static void
epoch_map_add__Zeta_Steel_EpochHashes_epoch_hashes_t(
  all_epoch_hashes a,
  uint32_t i,
  epoch_hashes_t x
)
{
  put__Zeta_Steel_EpochHashes_epoch_hashes_t(a, i, x);
}

static bool
update_ht(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint32_t e,
  record r,
  timestamp ts,
  uint16_t thread_id,
  htype ht
)
{
  get_result__Zeta_Steel_EpochHashes_epoch_hashes_t
  vopt = get__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes, e);
  if (vopt.tag == NotFound)
    return false;
  else if (vopt.tag == Fresh)
  {
    epoch_hashes_t eh = new_epoch(e);
    epoch_map_add__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes, e, eh);
    return update_ht(t, e, r, ts, thread_id, ht);
  }
  else if (vopt.tag == Found)
  {
    epoch_hashes_t v = vopt._0;
    stamped_record sr = { .record = r, .timestamp = ts, .thread_id = thread_id };
    uint32_t
    n = zeta__serialize_stamped_record((uint32_t)4096U, (uint32_t)0U, t.serialization_buffer, sr);
    ha ha0;
    if (ht == HAdd)
      ha0 = v.hadd;
    else
      ha0 = v.hevict;
    switch (ht)
    {
      case HAdd:
        {
          bool b = ha_add(v.hadd, n, t.serialization_buffer);
          return b;
        }
      case HEvict:
        {
          bool b = ha_add(v.hevict, n, t.serialization_buffer);
          return b;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
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
uu___is_Some__Zeta_Steel_ThreadStateModel_store_entry(
  option__Zeta_Steel_ThreadStateModel_store_entry projectee
)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

static void
maybe_update_high_water_mark__Zeta_Steel_EpochHashes_epoch_hashes_t(
  all_epoch_hashes a,
  uint32_t i
)
{
  option__uint32_t high = *a.high;
  bool r = above_high_water_mark(high, i);
  if (r)
    *a.high = ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = i });
}

static bool
vaddb_core(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  timestamp ts,
  uint16_t thread_id,
  record r
)
{
  bool b = check_slot_bounds(s);
  if (!b)
  {
    fail(t);
    return true;
  }
  else
  {
    Zeta_Steel_LogEntry_Types_key k = r.fst;
    Zeta_Steel_LogEntry_Types_value v = r.snd;
    if (is_root_key(k))
    {
      fail(t);
      return true;
    }
    else
    {
      option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
      option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
      option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
      option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
      if (uu___is_Some__Zeta_Steel_ThreadStateModel_store_entry(ropt))
      {
        fail(t);
        return true;
      }
      else
      {
        option__uint32_t lve = *t.last_verified_epoch;
        if (!epoch_greater_than_last_verified_epoch(lve, epoch_of_timestamp(ts)))
        {
          fail(t);
          return true;
        }
        else
        {
          bool ok = update_ht(t, epoch_of_timestamp(ts), r, ts, thread_id, HAdd);
          if (ok)
          {
            option__Zeta_Steel_LogEntry_Types_timestamp ts_opt = next(ts);
            if (ts_opt.tag == FStar_Pervasives_Native_None)
            {
              fail(t);
              return true;
            }
            else if (ts_opt.tag == FStar_Pervasives_Native_Some)
            {
              timestamp t_ = ts_opt.v;
              timestamp clock = *t.clock;
              timestamp next_clock = max(clock, t_);
              if (timestamp_lt(clock, next_clock))
              {
                *t.last_evict_key =
                  (
                    (Zeta_Steel_KeyUtils_raw_key){
                      .k = {
                        .v3 = (uint64_t)0U,
                        .v2 = (uint64_t)0U,
                        .v1 = (uint64_t)0U,
                        .v0 = (uint64_t)0U
                      },
                      .significant_digits = (uint16_t)0U
                    }
                  );
                *t.clock = next_clock;
                maybe_update_high_water_mark__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes,
                  next_clock.epoch);
                option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
                pt[as_u320(s)] =
                  (
                    (option__Zeta_Steel_ThreadStateModel_store_entry){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = mk_entry(k, v, BAdd)
                    }
                  );
                return true;
              }
              else
              {
                *t.clock = next_clock;
                maybe_update_high_water_mark__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes,
                  next_clock.epoch);
                option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
                pt[as_u320(s)] =
                  (
                    (option__Zeta_Steel_ThreadStateModel_store_entry){
                      .tag = FStar_Pervasives_Native_Some,
                      .v = mk_entry(k, v, BAdd)
                    }
                  );
                return true;
              }
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
            return ok;
        }
      }
    }
  }
}

static bool
vaddb(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  timestamp ts,
  uint16_t thread_id,
  record r
)
{
  bool b = vaddb_core(t, s, ts, thread_id, r);
  return b;
}

static void
evict_from_store(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_, bool d)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s_)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  if (res0.tag == FStar_Pervasives_Native_Some)
  {
    store_entry r_ = res0.v;
    store_entry e_;
    if (d)
      e_ =
        (
          (store_entry){
            .key = r_.key,
            .value = r_.value,
            .add_method = r_.add_method,
            .l_child_in_store = { .tag = FStar_Pervasives_Native_None },
            .r_child_in_store = r_.r_child_in_store,
            .parent_slot = r_.parent_slot
          }
        );
    else
      e_ =
        (
          (store_entry){
            .key = r_.key,
            .value = r_.value,
            .add_method = r_.add_method,
            .l_child_in_store = r_.l_child_in_store,
            .r_child_in_store = { .tag = FStar_Pervasives_Native_None },
            .parent_slot = r_.parent_slot
          }
        );
    option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
    pt[as_u320(s_)] =
      (
        (option__Zeta_Steel_ThreadStateModel_store_entry){
          .tag = FStar_Pervasives_Native_Some,
          .v = e_
        }
      );
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    pt0[as_u320(s)] =
      ((option__Zeta_Steel_ThreadStateModel_store_entry){ .tag = FStar_Pervasives_Native_None });
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

static bool uu___is_Some__uint16_t___bool(option__uint16_t___bool projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

static uint16_t fst__uint16_t_bool(__uint16_t_bool x)
{
  return x.fst;
}

static bool snd__uint16_t_bool(__uint16_t_bool x)
{
  return x.snd;
}

typedef struct
__FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry_FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry_s
{
  option__Zeta_Steel_ThreadStateModel_store_entry fst;
  option__Zeta_Steel_ThreadStateModel_store_entry snd;
}
__FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry_FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry;

static void vevictm_core(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_)
{
  if (!check_slot_bounds(s) || !check_slot_bounds(s_))
    *t.failed = true;
  else if (s == s_)
    *t.failed = true;
  else
  {
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s)];
    option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
    option__Zeta_Steel_ThreadStateModel_store_entry e = res0;
    option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res1 = pt[as_u320(s_)];
    option__Zeta_Steel_ThreadStateModel_store_entry res2 = res1;
    option__Zeta_Steel_ThreadStateModel_store_entry e_ = res2;
    __FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry_FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry
    scrut0 = { .fst = e, .snd = e_ };
    if (scrut0.fst.tag == FStar_Pervasives_Native_None)
      *t.failed = true;
    else if (scrut0.snd.tag == FStar_Pervasives_Native_None)
      *t.failed = true;
    else if
    (
      scrut0.fst.tag
      == FStar_Pervasives_Native_Some
      && scrut0.snd.tag == FStar_Pervasives_Native_Some
    )
    {
      store_entry r_ = scrut0.snd.v;
      store_entry r = scrut0.fst.v;
      Zeta_Steel_LogEntry_Types_key gk = r.key;
      Zeta_Steel_LogEntry_Types_value v = r.value;
      Zeta_Steel_LogEntry_Types_key gk_ = r_.key;
      Zeta_Steel_LogEntry_Types_value v_ = r_.value;
      Zeta_Steel_KeyUtils_raw_key k = to_base_key(gk);
      Zeta_Steel_KeyUtils_raw_key k_ = to_base_key(gk_);
      if (!is_proper_descendent(k, k_))
        *t.failed = true;
      else if (entry_points_to_some_slot(r, true) || entry_points_to_some_slot(r, false))
        *t.failed = true;
      else
      {
        bool d = desc_dir(k, k_);
        option__Zeta_Steel_LogEntry_Types_mval_value scrut = to_merkle_value(v_);
        if (scrut.tag == FStar_Pervasives_Native_Some)
        {
          Zeta_Steel_LogEntry_Types_mval_value v_1 = scrut.v;
          Zeta_Steel_LogEntry_Types_descendent_hash dh_ = desc_hash_dir(v_1, d);
          Zeta_Steel_KeyUtils_u256 h = hash_value(t.hasher, v);
          if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vnone)
            fail(t);
          else if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vsome)
          {
            Zeta_Steel_KeyUtils_raw_key k2 = dh_._0.dhd_key;
            if (!eq_base_key(k2, k))
              fail(t);
            else
            {
              bool has_parent_slot = uu___is_Some__uint16_t___bool(r.parent_slot);
              if (has_parent_slot)
              {
                __uint16_t_bool p_slot;
                if (r.parent_slot.tag == FStar_Pervasives_Native_Some)
                  p_slot = r.parent_slot.v;
                else
                  p_slot =
                    KRML_EABORT(__uint16_t_bool,
                      "unreachable (pattern matches are exhaustive in F*)");
                bool b1 = fst__uint16_t_bool(p_slot) != s_;
                bool b21 = snd__uint16_t_bool(p_slot) != d;
                if (b1 || b21)
                  fail(t);
                else
                {
                  Zeta_Steel_LogEntry_Types_mval_value
                  v__upd = update_merkle_value(v_1, d, k, h, false);
                  update_value(t,
                    s_,
                    (
                      (Zeta_Steel_LogEntry_Types_value){
                        .tag = Zeta_Steel_LogEntry_Types_MValue,
                        { .case_MValue = v__upd }
                      }
                    ));
                  evict_from_store(t, s, s_, d);
                }
              }
              else
              {
                bool b = entry_points_to_some_slot(r_, d);
                if (b)
                  fail(t);
                else
                {
                  Zeta_Steel_LogEntry_Types_mval_value
                  v__upd = update_merkle_value(v_1, d, k, h, false);
                  update_value(t,
                    s_,
                    (
                      (Zeta_Steel_LogEntry_Types_value){
                        .tag = Zeta_Steel_LogEntry_Types_MValue,
                        { .case_MValue = v__upd }
                      }
                    ));
                  evict_from_store(t, s, s_, d);
                }
              }
            }
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
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
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
}

static void vevictm(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_)
{
  vevictm_core(t, s, s_);
}

static bool
sat_evictb_checks(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, timestamp ts)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
  if (ropt.tag == FStar_Pervasives_Native_None)
    return false;
  else if (ropt.tag == FStar_Pervasives_Native_Some)
  {
    store_entry r = ropt.v;
    Zeta_Steel_LogEntry_Types_key k = r.key;
    Zeta_Steel_KeyUtils_raw_key bk = to_base_key(k);
    timestamp clock = *t.clock;
    Zeta_Steel_KeyUtils_raw_key lek = *t.last_evict_key;
    bool
    b =
      !is_root_key(k)
      &&
        tk_lt(((timestamp_key){ .fst = clock, .snd = lek }),
          ((timestamp_key){ .fst = ts, .snd = bk }))
      && !entry_points_to_some_slot(r, true)
      && !entry_points_to_some_slot(r, false);
    return b;
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
vevictb_update_hash_clock(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, timestamp ts)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  if (res0.tag == FStar_Pervasives_Native_Some)
  {
    store_entry r = res0.v;
    Zeta_Steel_LogEntry_Types_key k = r.key;
    Zeta_Steel_KeyUtils_raw_key bk = to_base_key(k);
    Zeta_Steel_LogEntry_Types_value v = r.value;
    uint32_t e = epoch_of_timestamp(ts);
    bool b = update_ht(t, e, ((record){ .fst = k, .snd = v }), ts, t.thread_id, HEvict);
    if (b)
    {
      *t.clock = ts;
      maybe_update_high_water_mark__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes, ts.epoch);
      *t.last_evict_key = bk;
      return b;
    }
    else
      return b;
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

static bool vevictb_core(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, timestamp ts)
{
  bool bounds_failed = !check_slot_bounds(s);
  if (bounds_failed)
  {
    *t.failed = true;
    return true;
  }
  else
  {
    bool b = sat_evictb_checks(t, s, ts);
    if (!b)
    {
      fail(t);
      return true;
    }
    else
    {
      option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
      option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
      option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
      if (res0.tag == FStar_Pervasives_Native_Some)
      {
        store_entry r = res0.v;
        if (r.add_method != BAdd)
        {
          fail(t);
          return true;
        }
        else
        {
          bool b1 = vevictb_update_hash_clock(t, s, ts);
          if (b1)
          {
            option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
            pt[as_u320(s)] =
              (
                (option__Zeta_Steel_ThreadStateModel_store_entry){
                  .tag = FStar_Pervasives_Native_None
                }
              );
            return true;
          }
          else
            return false;
        }
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
  }
}

static bool vevictb(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, timestamp ts)
{
  bool b = vevictb_core(t, s, ts);
  return b;
}

static bool uu___is_None__uint16_t___bool(option__uint16_t___bool projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_None)
    return true;
  else
    return false;
}

static bool
vevictbm_core(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_, timestamp ts)
{
  bool bounds_failed = !check_slot_bounds(s) || !check_slot_bounds(s_);
  if (bounds_failed)
    return fail_as(t);
  else if (s == s_)
    return fail_as(t);
  else
  {
    bool se_checks = sat_evictb_checks(t, s, ts);
    if (!se_checks)
      return fail_as(t);
    else
    {
      option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
      option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s_)];
      option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
      option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
      if (ropt.tag == FStar_Pervasives_Native_None)
        return fail_as(t);
      else if (ropt.tag == FStar_Pervasives_Native_Some)
      {
        store_entry r_ = ropt.v;
        option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
        option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u320(s)];
        option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
        if (res0.tag == FStar_Pervasives_Native_Some)
        {
          store_entry r = res0.v;
          if (r.add_method != MAdd)
          {
            bool b = fail_as(t);
            return b;
          }
          else
          {
            Zeta_Steel_LogEntry_Types_key gk = r.key;
            Zeta_Steel_LogEntry_Types_key gk_ = r_.key;
            Zeta_Steel_LogEntry_Types_value v_ = r_.value;
            Zeta_Steel_KeyUtils_raw_key k = to_base_key(gk);
            Zeta_Steel_KeyUtils_raw_key k_ = to_base_key(gk_);
            if (!is_proper_descendent(k, k_))
            {
              bool b = fail_as(t);
              return b;
            }
            else
            {
              option__Zeta_Steel_LogEntry_Types_mval_value scrut = to_merkle_value(v_);
              if (scrut.tag == FStar_Pervasives_Native_Some)
              {
                Zeta_Steel_LogEntry_Types_mval_value mv_ = scrut.v;
                bool d = desc_dir(k, k_);
                Zeta_Steel_LogEntry_Types_descendent_hash dh_ = desc_hash_dir(mv_, d);
                if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vnone)
                {
                  bool b = fail_as(t);
                  return b;
                }
                else if (dh_.tag == Zeta_Steel_LogEntry_Types_Dh_vsome)
                {
                  Zeta_Steel_LogEntry_Types_vbool b2 = dh_._0.evicted_to_blum;
                  Zeta_Steel_KeyUtils_u256 h2 = dh_._0.dhd_h;
                  Zeta_Steel_KeyUtils_raw_key k2 = dh_._0.dhd_key;
                  if (!eq_base_key(k2, k) || b2 == Zeta_Steel_LogEntry_Types_Vtrue)
                  {
                    bool b = fail_as(t);
                    return b;
                  }
                  else
                  {
                    bool parent_slot_none = uu___is_None__uint16_t___bool(r.parent_slot);
                    if (parent_slot_none)
                    {
                      bool b = fail_as(t);
                      return b;
                    }
                    else
                    {
                      __uint16_t_bool parent_slot;
                      if (r.parent_slot.tag == FStar_Pervasives_Native_Some)
                        parent_slot = r.parent_slot.v;
                      else
                        parent_slot =
                          KRML_EABORT(__uint16_t_bool,
                            "unreachable (pattern matches are exhaustive in F*)");
                      bool b1 = fst__uint16_t_bool(parent_slot) != s_;
                      bool b21 = snd__uint16_t_bool(parent_slot) != d;
                      if (b1 || b21)
                      {
                        bool b = fail_as(t);
                        return b;
                      }
                      else
                      {
                        bool b = vevictb_update_hash_clock(t, s, ts);
                        if (b)
                        {
                          Zeta_Steel_LogEntry_Types_mval_value
                          mv__upd = update_merkle_value(mv_, d, k, h2, true);
                          update_value(t,
                            s_,
                            (
                              (Zeta_Steel_LogEntry_Types_value){
                                .tag = Zeta_Steel_LogEntry_Types_MValue,
                                { .case_MValue = mv__upd }
                              }
                            ));
                          evict_from_store(t, s, s_, d);
                          return true;
                        }
                        else
                          return false;
                      }
                    }
                  }
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
              {
                KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
                  __FILE__,
                  __LINE__,
                  "unreachable (pattern matches are exhaustive in F*)");
                KRML_HOST_EXIT(255U);
              }
            }
          }
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
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
  }
}

static bool
vevictbm(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t s, uint16_t s_, timestamp ts)
{
  bool b = vevictbm_core(t, s, s_, ts);
  return b;
}

static void nextepoch_core(Zeta_Steel_VerifierTypes_thread_state_t t)
{
  timestamp c = *t.clock;
  uint32_t e = epoch_of_timestamp(c);
  option__uint32_t res = st_check_overflow_add32(e, (uint32_t)1U);
  if (res.tag == FStar_Pervasives_Native_None)
    fail(t);
  else if (res.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t nxt = res.v;
    timestamp c1 = { .epoch = nxt, .counter = (uint32_t)0U };
    *t.clock = c1;
    maybe_update_high_water_mark__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes, c1.epoch);
    *t.last_evict_key =
      (
        (Zeta_Steel_KeyUtils_raw_key){
          .k = { .v3 = (uint64_t)0U, .v2 = (uint64_t)0U, .v1 = (uint64_t)0U, .v0 = (uint64_t)0U },
          .significant_digits = (uint16_t)0U
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

static void nextepoch(Zeta_Steel_VerifierTypes_thread_state_t t)
{
  nextepoch_core(t);
}

static bool aggregate_epoch_hashes_t(epoch_hashes_t src, epoch_hashes_t dst)
{
  bool b = aggregate(dst.hadd, src.hadd);
  if (b)
  {
    bool b1 = aggregate(dst.hevict, src.hevict);
    if (b1)
      return true;
    else
      return false;
  }
  else
    return false;
}

static bool
propagate_epoch_hash(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  all_epoch_hashes hashes,
  uint32_t e
)
{
  get_result__Zeta_Steel_EpochHashes_epoch_hashes_t
  dst = get__Zeta_Steel_EpochHashes_epoch_hashes_t(hashes, e);
  if (dst.tag == NotFound)
    return false;
  else if (dst.tag == Fresh)
  {
    epoch_hashes_t eh = new_epoch(e);
    epoch_map_add__Zeta_Steel_EpochHashes_epoch_hashes_t(hashes, e, eh);
    return propagate_epoch_hash(t, hashes, e);
  }
  else if (dst.tag == Found)
  {
    epoch_hashes_t dst1 = dst._0;
    get_result__Zeta_Steel_EpochHashes_epoch_hashes_t
    src = get__Zeta_Steel_EpochHashes_epoch_hashes_t(t.epoch_hashes, e);
    if (src.tag == NotFound)
      return false;
    else if (src.tag == Fresh)
      return false;
    else if (src.tag == Found)
    {
      epoch_hashes_t src1 = src._0;
      bool b = aggregate_epoch_hashes_t(src1, dst1);
      if (b)
        return true;
      else
        return false;
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
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static void put__Prims_dtuple2__bool____(epoch_tid_bitmaps a, uint32_t i, bool *x)
{
  uint32_t idx = i % a.etbl.store_len;
  option__K___uint32_t_Prims_dtuple2__bool____ *pt = a.etbl.store;
  pt[idx] =
    (
      (option__K___uint32_t_Prims_dtuple2__bool____){
        .tag = FStar_Pervasives_Native_Some,
        .v = { .fst = i, .snd = x }
      }
    );
  option__uint32_t high = *a.high;
  bool r = above_high_water_mark(high, i);
  if (r)
    *a.high = ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = i });
}

static bool update_bitmap(epoch_tid_bitmaps tid_bitmaps, uint32_t e, uint16_t tid)
{
  get_result__Prims_dtuple2___bool____ res = get__Prims_dtuple2__bool____(tid_bitmaps, e);
  if (res.tag == NotFound)
    return false;
  else if (res.tag == Fresh)
  {
    KRML_CHECK_SIZE(sizeof (bool), Zeta_Steel_ApplicationTypes_n_threads);
    bool *p = KRML_HOST_MALLOC(sizeof (bool) * Zeta_Steel_ApplicationTypes_n_threads);
    for (uint32_t _i = 0U; _i < Zeta_Steel_ApplicationTypes_n_threads; ++_i)
      p[_i] = false;
    bool *res1 = p;
    bool *new_bm = res1;
    bool *pt = new_bm;
    pt[as_u320(tid)] = true;
    put__Prims_dtuple2__bool____(tid_bitmaps, e, new_bm);
    return true;
  }
  else if (res.tag == Found)
  {
    bool *v = res._0;
    bool *pt = v;
    pt[as_u320(tid)] = true;
    return true;
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
verify_epoch_core(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  all_epoch_hashes hashes,
  epoch_tid_bitmaps tid_bitmaps,
  cancellable_lock lock
)
{
  option__uint32_t e = *t.last_verified_epoch;
  option__uint32_t e_ = maybe_increment_last_verified_epoch(e);
  if (e_.tag == FStar_Pervasives_Native_None)
  {
    *t.failed = true;
    return true;
  }
  else if (e_.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t e1 = e_.v;
    timestamp clock = *t.clock;
    if (epoch_of_timestamp(clock) == e1)
    {
      *t.failed = true;
      return true;
    }
    else
    {
      bool acquired = acquire0(lock);
      if (!acquired)
        return false;
      else
      {
        bool b0 = propagate_epoch_hash(t, hashes, e1);
        bool b1 = update_bitmap(tid_bitmaps, e1, t.thread_id);
        if (!b0 || !b1)
        {
          cancel(lock);
          return false;
        }
        else
        {
          *t.last_verified_epoch =
            ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = e1 });
          release_lock(lock);
          return true;
        }
      }
    }
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

static bool verify_epoch(Zeta_Steel_VerifierTypes_thread_state_t t, aggregate_epoch_hashes aeh)
{
  bool b = verify_epoch_core(t, aeh.hashes, aeh.tid_bitmaps, aeh.lock);
  return b;
}

static Zeta_Steel_VerifierTypes_thread_state_t create_basic(uint16_t tid)
{
  KRML_CHECK_SIZE(sizeof (bool), (uint32_t)1U);
  bool *failed = KRML_HOST_MALLOC(sizeof (bool));
  failed[0U] = false;
  KRML_CHECK_SIZE(sizeof (option__Zeta_Steel_ThreadStateModel_store_entry),
    as_u320(Zeta_Steel_ApplicationTypes_store_size));
  option__Zeta_Steel_ThreadStateModel_store_entry
  *p0 =
    KRML_HOST_MALLOC(sizeof (option__Zeta_Steel_ThreadStateModel_store_entry)
      * as_u320(Zeta_Steel_ApplicationTypes_store_size));
  for (uint32_t _i = 0U; _i < as_u320(Zeta_Steel_ApplicationTypes_store_size); ++_i)
    p0[_i]
    = ((option__Zeta_Steel_ThreadStateModel_store_entry){ .tag = FStar_Pervasives_Native_None });
  option__Zeta_Steel_ThreadStateModel_store_entry *res = p0;
  option__Zeta_Steel_ThreadStateModel_store_entry *store = res;
  KRML_CHECK_SIZE(sizeof (timestamp), (uint32_t)1U);
  timestamp *clock = KRML_HOST_MALLOC(sizeof (timestamp));
  clock[0U] = ((timestamp){ .epoch = (uint32_t)0U, .counter = (uint32_t)0U });
  KRML_CHECK_SIZE(sizeof (Zeta_Steel_KeyUtils_raw_key), (uint32_t)1U);
  Zeta_Steel_KeyUtils_raw_key
  *last_evict_key = KRML_HOST_MALLOC(sizeof (Zeta_Steel_KeyUtils_raw_key));
  last_evict_key[0U]
  =
    (
      (Zeta_Steel_KeyUtils_raw_key){
        .k = { .v3 = (uint64_t)0U, .v2 = (uint64_t)0U, .v1 = (uint64_t)0U, .v0 = (uint64_t)0U },
        .significant_digits = (uint16_t)0U
      }
    );
  all_epoch_hashes epoch_hashes = create__Zeta_Steel_EpochHashes_epoch_hashes_t((uint32_t)64U);
  KRML_CHECK_SIZE(sizeof (option__uint32_t), (uint32_t)1U);
  option__uint32_t *last_verified_epoch = KRML_HOST_MALLOC(sizeof (option__uint32_t));
  last_verified_epoch[0U] = ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  uint8_t *p = KRML_HOST_CALLOC((uint32_t)4096U, sizeof (uint8_t));
  uint8_t *res0 = p;
  uint8_t *serialization_buffer = res0;
  hasher_t hasher = alloc();
  return
    (
      (Zeta_Steel_VerifierTypes_thread_state_t){
        .thread_id = tid,
        .failed = failed,
        .store = store,
        .clock = clock,
        .last_evict_key = last_evict_key,
        .epoch_hashes = epoch_hashes,
        .last_verified_epoch = last_verified_epoch,
        .serialization_buffer = serialization_buffer,
        .hasher = hasher
      }
    );
}

static void
madd_to_store_root(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t s,
  Zeta_Steel_LogEntry_Types_value v
)
{
  bool
  b =
    is_value_of((
        (Zeta_Steel_LogEntry_Types_key){
          .tag = Zeta_Steel_LogEntry_Types_InternalKey,
          {
            .case_InternalKey = {
              .k = {
                .v3 = (uint64_t)0U,
                .v2 = (uint64_t)0U,
                .v1 = (uint64_t)0U,
                .v0 = (uint64_t)0U
              },
              .significant_digits = (uint16_t)0U
            }
          }
        }
      ),
      v);
  if (!!b)
  {
    option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
    option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u320(s)];
    option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
    option__Zeta_Steel_ThreadStateModel_store_entry ropt = res0;
    if (!(ropt.tag == FStar_Pervasives_Native_Some))
    {
      store_entry
      new_entry =
        {
          .key = {
            .tag = Zeta_Steel_LogEntry_Types_InternalKey,
            {
              .case_InternalKey = {
                .k = {
                  .v3 = (uint64_t)0U,
                  .v2 = (uint64_t)0U,
                  .v1 = (uint64_t)0U,
                  .v0 = (uint64_t)0U
                },
                .significant_digits = (uint16_t)0U
              }
            }
          }, .value = v, .add_method = MAdd,
          .l_child_in_store = { .tag = FStar_Pervasives_Native_None },
          .r_child_in_store = { .tag = FStar_Pervasives_Native_None },
          .parent_slot = { .tag = FStar_Pervasives_Native_None }
        };
      option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
      pt[as_u320(s)] =
        (
          (option__Zeta_Steel_ThreadStateModel_store_entry){
            .tag = FStar_Pervasives_Native_Some,
            .v = new_entry
          }
        );
    }
  }
}

static Zeta_Steel_VerifierTypes_thread_state_t create1(uint16_t tid)
{
  Zeta_Steel_VerifierTypes_thread_state_t ts = create_basic(tid);
  if (tid == (uint16_t)0U)
  {
    madd_to_store_root(ts,
      (uint16_t)0U,
      init_value((
          (Zeta_Steel_LogEntry_Types_key){
            .tag = Zeta_Steel_LogEntry_Types_InternalKey,
            {
              .case_InternalKey = {
                .k = {
                  .v3 = (uint64_t)0U,
                  .v2 = (uint64_t)0U,
                  .v1 = (uint64_t)0U,
                  .v0 = (uint64_t)0U
                },
                .significant_digits = (uint16_t)0U
              }
            }
          }
        )));
    return ts;
  }
  else
    return ts;
}

static bool uu___is_Verify_success(Zeta_Steel_Verifier_verify_result projectee)
{
  if (projectee.tag == Zeta_Steel_Verifier_Verify_success)
    return true;
  else
    return false;
}

static void fail0()
{

}

static option__uint32_t verify_entry_cases(bool b)
{
  if (b)
    return ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = (uint32_t)0U });
  else
  {
    fail0();
    return ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
  }
}

static option__uint32_t
verify_log_entry(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  aggregate_epoch_hashes aeh,
  log_entry le
)
{
  if (le.tag == VerifyEpoch)
  {
    bool b = verify_epoch(t, aeh);
    if (b)
      return ((option__uint32_t){ .tag = FStar_Pervasives_Native_Some, .v = (uint32_t)0U });
    else
    {
      fail0();
      return ((option__uint32_t){ .tag = FStar_Pervasives_Native_None });
    }
  }
  else if (le.tag == AddM)
  {
    record r = le.case_AddM.r;
    uint16_t s_ = le.case_AddM.s_;
    uint16_t s = le.case_AddM.s;
    bool b = vaddm(t, s, s_, r);
    return verify_entry_cases(b);
  }
  else if (le.tag == AddB)
  {
    record r = le.case_AddB.r;
    uint16_t tid = le.case_AddB.tid;
    timestamp ts = le.case_AddB.ts;
    uint16_t s = le.case_AddB.s;
    bool b = vaddb(t, s, ts, tid, r);
    return verify_entry_cases(b);
  }
  else if (le.tag == EvictM)
  {
    evictM_payload pl = le.case_EvictM;
    vevictm(t, pl.s, pl.s_);
    return verify_entry_cases(true);
  }
  else if (le.tag == EvictB)
  {
    evictB_payload pl = le.case_EvictB;
    bool b = vevictb(t, pl.s1, pl.t);
    return verify_entry_cases(b);
  }
  else if (le.tag == EvictBM)
  {
    evictBM_payload pl = le.case_EvictBM;
    bool b = vevictbm(t, pl.s2, pl.s_1, pl.t1);
    return verify_entry_cases(b);
  }
  else if (le.tag == NextEpoch)
  {
    nextepoch(t);
    return verify_entry_cases(true);
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

static Zeta_Steel_Verifier_verify_result
verify_step(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint32_t len,
  uint32_t log_pos,
  uint8_t *log,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  aggregate_epoch_hashes aeh
)
{
  option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t
  res = zeta__parser_log_entry(len, log_pos, len - log_pos, log);
  if (res.tag == FStar_Pervasives_Native_None)
    return
      (
        (Zeta_Steel_Verifier_verify_result){
          .tag = Zeta_Steel_Verifier_Parsing_failure,
          { .case_Parsing_failure = log_pos }
        }
      );
  else if (res.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t read = res.v.snd;
    log_entry le = res.v.fst;
    if (le.tag == RunApp)
    {
      runApp_payload pl = le.case_RunApp;
      uint32_t pl_pos0 = zeta__runapp_payload_offset(le);
      uint32_t pl_pos = log_pos + pl_pos0;
      verify_runapp_result
      app_res =
        Zeta_Steel_Application_run_app_function(len,
          pl,
          pl_pos,
          log,
          out_len,
          out_offset,
          out,
          t);
      if (app_res.tag == Run_app_parsing_failure)
        return
          (
            (Zeta_Steel_Verifier_verify_result){
              .tag = Zeta_Steel_Verifier_App_failure,
              { .case_App_failure = log_pos }
            }
          );
      else if (app_res.tag == Run_app_verify_failure)
        return
          (
            (Zeta_Steel_Verifier_verify_result){
              .tag = Zeta_Steel_Verifier_App_failure,
              { .case_App_failure = log_pos }
            }
          );
      else if (app_res.tag == Run_app_success)
      {
        uint32_t written = app_res.wrote;
        return
          (
            (Zeta_Steel_Verifier_verify_result){
              .tag = Zeta_Steel_Verifier_Verify_success,
              { .case_Verify_success = { .read = read, .wrote = written } }
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
    {
      option__uint32_t b = verify_log_entry(t, aeh, le);
      if (b.tag == FStar_Pervasives_Native_None)
        return
          (
            (Zeta_Steel_Verifier_verify_result){
              .tag = Zeta_Steel_Verifier_Verify_entry_failure,
              { .case_Verify_entry_failure = log_pos }
            }
          );
      else if (b.tag == FStar_Pervasives_Native_Some)
      {
        uint32_t written = b.v;
        return
          (
            (Zeta_Steel_Verifier_verify_result){
              .tag = Zeta_Steel_Verifier_Verify_success,
              { .case_Verify_success = { .read = read, .wrote = written } }
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

static Zeta_Steel_Verifier_verify_result
verify_log_ind(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint32_t len,
  uint8_t *log,
  uint32_t log_pos,
  uint32_t outlen,
  uint32_t out_pos,
  uint8_t *out,
  aggregate_epoch_hashes aeh
)
{
  uint32_t r = (uint32_t)0U;
  uint32_t r1 = (uint32_t)0U;
  Zeta_Steel_Verifier_verify_result
  r2 =
    {
      .tag = Zeta_Steel_Verifier_Verify_success,
      { .case_Verify_success = { .read = (uint32_t)0U, .wrote = (uint32_t)0U } }
    };
  r = log_pos;
  Zeta_Steel_Verifier_verify_result
  res =
    {
      .tag = Zeta_Steel_Verifier_Verify_success,
      { .case_Verify_success = { .read = log_pos, .wrote = out_pos } }
    };
  r2 = res;
  r1 = out_pos;
  Zeta_Steel_Verifier_verify_result res0 = r2;
  uint32_t log_pos10 = r;
  bool b = uu___is_Verify_success(res0) && log_pos10 < len;
  bool cond = b;
  while (cond)
  {
    uint32_t log_pos10 = r;
    uint32_t out_pos1 = r1;
    bool is_failed = check_failed(t);
    if (is_failed)
    {
      Zeta_Steel_Verifier_verify_result
      res =
        {
          .tag = Zeta_Steel_Verifier_Verify_entry_failure,
          { .case_Verify_entry_failure = log_pos10 }
        };
      r2 = res;
    }
    else
    {
      Zeta_Steel_Verifier_verify_result
      res = verify_step(t, len, log_pos10, log, outlen, out_pos1, out, aeh);
      if (res.tag == Zeta_Steel_Verifier_Parsing_failure)
      {
        uint32_t loc = res.case_Parsing_failure;
        Zeta_Steel_Verifier_verify_result
        res_ = { .tag = Zeta_Steel_Verifier_Parsing_failure, { .case_Parsing_failure = loc } };
        r2 = res_;
      }
      else if (res.tag == Zeta_Steel_Verifier_App_failure)
      {
        uint32_t loc = res.case_App_failure;
        Zeta_Steel_Verifier_verify_result
        res_ = { .tag = Zeta_Steel_Verifier_App_failure, { .case_App_failure = loc } };
        r2 = res_;
      }
      else if (res.tag == Zeta_Steel_Verifier_Verify_entry_failure)
      {
        Zeta_Steel_Verifier_verify_result res_ = res;
        r2 = res_;
      }
      else if (res.tag == Zeta_Steel_Verifier_Verify_success)
      {
        uint32_t wrote = res.case_Verify_success.wrote;
        uint32_t read = res.case_Verify_success.read;
        Zeta_Steel_Verifier_verify_result
        res_ =
          {
            .tag = Zeta_Steel_Verifier_Verify_success,
            { .case_Verify_success = { .read = log_pos10 + read, .wrote = out_pos1 + wrote } }
          };
        uint32_t log_pos2 = log_pos10 + read;
        uint32_t out_pos2 = out_pos1 + wrote;
        r2 = res_;
        r = log_pos2;
        r1 = out_pos2;
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
    Zeta_Steel_Verifier_verify_result res = r2;
    uint32_t log_pos1 = r;
    bool b = uu___is_Verify_success(res) && log_pos1 < len;
    cond = b;
  }
  Zeta_Steel_Verifier_verify_result v = r2;
  Zeta_Steel_Verifier_verify_result v0 = v;
  Zeta_Steel_Verifier_verify_result v1 = v0;
  Zeta_Steel_Verifier_verify_result res1 = v1;
  return res1;
}

static Zeta_Steel_Verifier_verify_result
verify_log(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint32_t len,
  uint8_t *log,
  uint32_t outlen,
  uint8_t *out,
  aggregate_epoch_hashes aeh
)
{
  return verify_log_ind(t, len, log, (uint32_t)0U, outlen, (uint32_t)0U, out, aeh);
}

typedef struct thread_state_s
{
  uint16_t tid;
  Zeta_Steel_VerifierTypes_thread_state_t tsm;
  cancellable_lock lock;
}
thread_state;

typedef thread_state *all_threads_t;

typedef struct Zeta_Steel_Main_top_level_state_s
{
  aggregate_epoch_hashes aeh;
  thread_state *all_threads;
}
Zeta_Steel_Main_top_level_state;

static thread_state init_thread_state(uint16_t i)
{
  Zeta_Steel_VerifierTypes_thread_state_t st = create1(i);
  cancellable_lock lock = new_cancellable_lock();
  return ((thread_state){ .tid = i, .tsm = st, .lock = lock });
}

static void init_all_threads_state(thread_state *all_threads, uint16_t i)
{
  bool b = (uint32_t)i == Zeta_Steel_ApplicationTypes_n_threads;
  if (!b)
  {
    thread_state st = init_thread_state(i);
    thread_state *pt = all_threads;
    pt[(uint32_t)i] = st;
    init_all_threads_state(all_threads, i + (uint16_t)1U);
  }
}

Zeta_Steel_Main_top_level_state *Zeta_Steel_Main_init()
{
  aggregate_epoch_hashes aeh = create0();
  thread_state st0 = init_thread_state((uint16_t)0U);
  KRML_CHECK_SIZE(sizeof (thread_state), Zeta_Steel_ApplicationTypes_n_threads);
  thread_state
  *p = KRML_HOST_MALLOC(sizeof (thread_state) * Zeta_Steel_ApplicationTypes_n_threads);
  for (uint32_t _i = 0U; _i < Zeta_Steel_ApplicationTypes_n_threads; ++_i)
    p[_i] = st0;
  thread_state *res = p;
  thread_state *all_threads = res;
  init_all_threads_state(all_threads, (uint16_t)1U);
  Zeta_Steel_Main_top_level_state r = { .aeh = aeh, .all_threads = all_threads };
  KRML_CHECK_SIZE(sizeof (Zeta_Steel_Main_top_level_state), (uint32_t)1U);
  Zeta_Steel_Main_top_level_state
  *t = KRML_HOST_MALLOC(sizeof (Zeta_Steel_Main_top_level_state));
  t[0U] = r;
  return t;
}

static FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
verify_log_aux(
  Zeta_Steel_Main_top_level_state t,
  uint16_t tid,
  uint32_t len,
  uint8_t *input,
  uint32_t out_len,
  uint8_t *output
)
{
  thread_state *pt = t.all_threads;
  thread_state st_tid = pt[(uint32_t)tid];
  bool b = acquire0(st_tid.lock);
  if (b == false)
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    Zeta_Steel_Verifier_verify_result
    vr = verify_log(st_tid.tsm, len, input, out_len, output, t.aeh);
    if (vr.tag == Zeta_Steel_Verifier_Verify_success)
    {
      bool b_failed = check_failed(st_tid.tsm);
      if (b_failed)
      {
        cancel(st_tid.lock);
        return
          (
            (FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result){
              .tag = FStar_Pervasives_Native_None
            }
          );
      }
      else
      {
        release0(st_tid.lock);
        return
          (
            (FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result){
              .tag = FStar_Pervasives_Native_Some,
              .v = vr
            }
          );
      }
    }
    else
    {
      cancel(st_tid.lock);
      return
        (
          (FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result){
            .tag = FStar_Pervasives_Native_None
          }
        );
    }
  }
}

FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
Zeta_Steel_Main_verify_log(
  Zeta_Steel_Main_top_level_state *r,
  uint16_t tid,
  uint32_t len,
  uint8_t *input,
  uint32_t out_len,
  uint8_t *output
)
{
  Zeta_Steel_Main_top_level_state t_ = *r;
  FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
  res = verify_log_aux(t_, tid, len, input, out_len, output);
  return res;
}

Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
Zeta_Steel_Main_max_certified_epoch(Zeta_Steel_Main_top_level_state *r)
{
  Zeta_Steel_Main_top_level_state t_ = *r;
  Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
  res = advance_and_read_max_certified_epoch(t_.aeh);
  if (res.tag == Zeta_Steel_AggregateEpochHashes_Read_max_error)
    return
      (
        (Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result){
          .tag = Zeta_Steel_AggregateEpochHashes_Read_max_error
        }
      );
  else if (res.tag == Zeta_Steel_AggregateEpochHashes_Read_max_none)
    return
      (
        (Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result){
          .tag = Zeta_Steel_AggregateEpochHashes_Read_max_none
        }
      );
  else if (res.tag == Zeta_Steel_AggregateEpochHashes_Read_max_some)
  {
    uint32_t max = res._0;
    return
      (
        (Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result){
          .tag = Zeta_Steel_AggregateEpochHashes_Read_max_some,
          ._0 = max
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

FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv
Zeta_Steel_Main_read_store(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t slot)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt[as_u32(slot)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  option__Zeta_Steel_ThreadStateModel_store_entry se_opt = res0;
  if (se_opt.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (se_opt.tag == FStar_Pervasives_Native_Some)
  {
    store_entry se = se_opt.v;
    store_entry se1 = se;
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .key = se1.key, .value = se1.value }
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

void
Zeta_Steel_Main_write_store(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t slot,
  Zeta_Steel_LogEntry_Types_value v
)
{
  option__Zeta_Steel_ThreadStateModel_store_entry *pt0 = t.store;
  option__Zeta_Steel_ThreadStateModel_store_entry res = pt0[as_u32(slot)];
  option__Zeta_Steel_ThreadStateModel_store_entry res0 = res;
  option__Zeta_Steel_ThreadStateModel_store_entry se_opt = res0;
  if (se_opt.tag == FStar_Pervasives_Native_Some)
  {
    store_entry se = se_opt.v;
    store_entry se1 = se;
    store_entry
    se_ =
      {
        .key = se1.key, .value = v, .add_method = se1.add_method,
        .l_child_in_store = se1.l_child_in_store, .r_child_in_store = se1.r_child_in_store,
        .parent_slot = se1.parent_slot
      };
    option__Zeta_Steel_ThreadStateModel_store_entry *pt = t.store;
    pt[as_u32(slot)] =
      (
        (option__Zeta_Steel_ThreadStateModel_store_entry){
          .tag = FStar_Pervasives_Native_Some,
          .v = se_
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

