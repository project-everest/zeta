

#include "ZetaFormats.h"

#define VALIDATOR_MAX_LENGTH (4294967295ULL)

static inline bool is_error(uint64_t positionOrError)
{
  return positionOrError > VALIDATOR_MAX_LENGTH;
}

#define VALIDATOR_ERROR_GENERIC (4294967296ULL)

#define VALIDATOR_ERROR_NOT_ENOUGH_DATA (8589934592ULL)

typedef struct timestamp_s
{
  uint32_t epoch;
  uint32_t counter;
}
timestamp;

typedef struct timestamp__s
{
  uint32_t fst;
  uint32_t snd;
}
timestamp_;

static uint32_t timestamp_size32(timestamp input)
{
  KRML_MAYBE_UNUSED_VAR(input);
  uint32_t v1 = 4U;
  uint32_t v2 = 4U;
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t timestamp_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 8ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 8ULL;
}

static uint32_t timestamp_jumper(uint32_t pos)
{
  return pos + 8U;
}

static timestamp timestamp_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t x1 = load32_be(input.base + pos);
  uint32_t pos2 = pos + 4U;
  uint32_t x2 = load32_be(input.base + pos2);
  timestamp_ res = { .fst = x1, .snd = x2 };
  uint32_t epoch = res.fst;
  uint32_t counter = res.snd;
  return ((timestamp){ .epoch = epoch, .counter = counter });
}

static uint32_t timestamp_lserializer(timestamp x, uint8_t *input, uint32_t pos)
{
  store32_be(input + pos, x.epoch);
  uint32_t res = 4U;
  uint32_t len1 = res;
  uint32_t pos1 = pos + len1;
  store32_be(input + pos1, x.counter);
  uint32_t res0 = 4U;
  uint32_t len2 = res0;
  return len1 + len2;
}

static uint32_t slot_id_size32(uint16_t x)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return 2U;
}

static uint64_t slot_id_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 2ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 2ULL;
}

static uint32_t slot_id_jumper(uint32_t pos)
{
  return pos + 2U;
}

static uint16_t slot_id_reader(LowParse_Slice_slice sl, uint32_t pos)
{
  return load16_be(sl.base + pos);
}

typedef struct evictbm_payload_s
{
  uint16_t evictbm_s;
  uint16_t evictbm_s2;
  timestamp evictbm_t;
}
evictbm_payload;

typedef struct __uint16_t_uint16_t_s
{
  uint16_t fst;
  uint16_t snd;
}
__uint16_t_uint16_t;

typedef struct evictbm_payload__s
{
  __uint16_t_uint16_t fst;
  timestamp snd;
}
evictbm_payload_;

static uint32_t evictbm_payload_size32(evictbm_payload input)
{
  uint32_t v10 = slot_id_size32(input.evictbm_s);
  uint32_t v20 = slot_id_size32(input.evictbm_s2);
  uint32_t v1;
  if (4294967295U - v20 < v10)
    v1 = 4294967295U;
  else
    v1 = v10 + v20;
  uint32_t v2 = timestamp_size32(input.evictbm_t);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t evictbm_payload_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 12ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 12ULL;
}

static uint32_t evictbm_payload_jumper(uint32_t pos)
{
  return pos + 12U;
}

static evictbm_payload evictbm_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint16_t x1 = slot_id_reader(input, pos);
  uint32_t pos20 = slot_id_jumper(pos);
  uint16_t x2 = slot_id_reader(input, pos20);
  __uint16_t_uint16_t x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = slot_id_jumper(slot_id_jumper(pos));
  timestamp x20 = timestamp_reader(input, pos2);
  evictbm_payload_ res = { .fst = x10, .snd = x20 };
  timestamp evictbm_t = res.snd;
  uint16_t evictbm_s2 = res.fst.snd;
  uint16_t evictbm_s = res.fst.fst;
  return
    ((evictbm_payload){ .evictbm_s = evictbm_s, .evictbm_s2 = evictbm_s2, .evictbm_t = evictbm_t });
}

static timestamp_ bit_offset_in_word(uint16_t i)
{
  if (i < 64U)
    return ((timestamp_){ .fst = 0U, .snd = (uint32_t)i });
  else if (i < 128U)
    return ((timestamp_){ .fst = 1U, .snd = (uint32_t)((uint32_t)i - 64U) });
  else if (i < 192U)
    return ((timestamp_){ .fst = 2U, .snd = (uint32_t)((uint32_t)i - 128U) });
  else
    return ((timestamp_){ .fst = 3U, .snd = (uint32_t)((uint32_t)i - 192U) });
}

static uint64_t truncate_word(uint64_t k, uint32_t index)
{
  if (index == 0U)
    return 0ULL;
  else
  {
    uint32_t shift_index = 64U - index;
    uint64_t mask = 0xffffffffffffffffULL >> shift_index;
    return k & mask;
  }
}

static Zeta_Steel_KeyUtils_raw_key truncate_key(Zeta_Steel_KeyUtils_raw_key k, uint16_t w)
{
  if (w == 256U)
    return k;
  else
  {
    timestamp_ scrut = bit_offset_in_word(w);
    uint32_t word = scrut.fst;
    uint32_t index = scrut.snd;
    Zeta_Steel_KeyUtils_u256 kk = k.k;
    Zeta_Steel_KeyUtils_u256 kk_;
    if (word == 0U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = 0ULL,
            .v2 = 0ULL,
            .v1 = 0ULL,
            .v0 = truncate_word(kk.v0, index)
          }
        );
    else if (word == 1U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = 0ULL,
            .v2 = 0ULL,
            .v1 = truncate_word(kk.v1, index),
            .v0 = kk.v0
          }
        );
    else if (word == 2U)
      kk_ =
        (
          (Zeta_Steel_KeyUtils_u256){
            .v3 = 0ULL,
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

static bool is_internal_key(Zeta_Steel_KeyUtils_raw_key r)
{
  return r.significant_digits < 256U;
}

static uint32_t application_value_size32(Zeta_Steel_ApplicationTypes_value_type x)
{
  return Zeta_Formats_Aux_Application_value_Size_application_value_size32(x);
}

static uint64_t application_value_validator(LowParse_Slice_slice input, uint64_t pos)
{
  return Zeta_Formats_Aux_Application_value_Low_application_value_validator(input, pos);
}

static uint32_t application_value_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return Zeta_Formats_Aux_Application_value_Low_application_value_jumper(input, pos);
}

static Zeta_Steel_ApplicationTypes_value_type
application_value_reader(LowParse_Slice_slice input, uint32_t pos)
{
  return Zeta_Formats_Aux_Application_value_Low_application_value_reader(input, pos);
}

static uint32_t
application_value_lserializer(
  Zeta_Steel_ApplicationTypes_value_type v,
  uint8_t *output,
  uint32_t pos
)
{
  return Zeta_Formats_Aux_Application_value_Low_application_value_lserializer(v, output, pos);
}

static uint32_t application_key_size32(Zeta_Steel_ApplicationTypes_key_type x)
{
  return Zeta_Formats_Aux_Application_key_Size_application_key_size32(x);
}

static uint64_t application_key_validator(LowParse_Slice_slice input, uint64_t pos)
{
  return Zeta_Formats_Aux_Application_key_Low_application_key_validator(input, pos);
}

static uint32_t application_key_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return Zeta_Formats_Aux_Application_key_Low_application_key_jumper(input, pos);
}

static Zeta_Steel_ApplicationTypes_key_type
application_key_reader(LowParse_Slice_slice input, uint32_t pos)
{
  return Zeta_Formats_Aux_Application_key_Low_application_key_reader(input, pos);
}

static uint32_t
application_key_lserializer(
  Zeta_Steel_ApplicationTypes_key_type v,
  uint8_t *output,
  uint32_t pos
)
{
  return Zeta_Formats_Aux_Application_key_Low_application_key_lserializer(v, output, pos);
}

typedef uint32_t uninterpreted;

static uint64_t significant_digits_t_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t res;
  if ((uint64_t)input.len - pos < 2ULL)
    res = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    res = pos + 2ULL;
  if (is_error(res))
    return res;
  else
  {
    uint16_t va = load16_be(input.base + (uint32_t)pos);
    if (!(va <= 256U))
      return VALIDATOR_ERROR_GENERIC;
    else
      return res;
  }
}

static uint16_t significant_digits_t_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint16_t res = load16_be(input.base + pos);
  return res;
}

static uint32_t significant_digits_t_lserializer(uint16_t x, uint8_t *input, uint32_t pos)
{
  store16_be(input + pos, x);
  return 2U;
}

typedef struct u256_s
{
  uint64_t v3;
  uint64_t v2;
  uint64_t v1;
  uint64_t v0;
}
u256;

typedef struct __uint64_t_uint64_t_s
{
  uint64_t fst;
  uint64_t snd;
}
__uint64_t_uint64_t;

typedef struct u256__s
{
  __uint64_t_uint64_t fst;
  __uint64_t_uint64_t snd;
}
u256_;

static uint32_t u256_size32(u256 input)
{
  KRML_MAYBE_UNUSED_VAR(input);
  uint32_t v10 = 8U;
  uint32_t v20 = 8U;
  uint32_t v1;
  if (4294967295U - v20 < v10)
    v1 = 4294967295U;
  else
    v1 = v10 + v20;
  uint32_t v11 = 8U;
  uint32_t v21 = 8U;
  uint32_t v2;
  if (4294967295U - v21 < v11)
    v2 = 4294967295U;
  else
    v2 = v11 + v21;
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t u256_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 32ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 32ULL;
}

static uint32_t u256_jumper(uint32_t pos)
{
  return pos + 32U;
}

static u256 u256_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint64_t x1 = load64_be(input.base + pos);
  uint32_t pos20 = pos + 8U;
  uint64_t x2 = load64_be(input.base + pos20);
  __uint64_t_uint64_t x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = pos + 8U + 8U;
  uint64_t x11 = load64_be(input.base + pos2);
  uint32_t pos21 = pos2 + 8U;
  uint64_t x20 = load64_be(input.base + pos21);
  __uint64_t_uint64_t x21 = { .fst = x11, .snd = x20 };
  u256_ res = { .fst = x10, .snd = x21 };
  uint64_t v0 = res.snd.snd;
  uint64_t v1 = res.snd.fst;
  uint64_t v2 = res.fst.snd;
  uint64_t v3 = res.fst.fst;
  return ((u256){ .v3 = v3, .v2 = v2, .v1 = v1, .v0 = v0 });
}

static uint32_t u256_lserializer(u256 x, uint8_t *input, uint32_t pos)
{
  store64_be(input + pos, x.v3);
  uint32_t res0 = 8U;
  uint32_t len1 = res0;
  uint32_t pos10 = pos + len1;
  store64_be(input + pos10, x.v2);
  uint32_t res1 = 8U;
  uint32_t len2 = res1;
  uint32_t res2 = len1 + len2;
  uint32_t len10 = res2;
  uint32_t pos1 = pos + len10;
  store64_be(input + pos1, x.v1);
  uint32_t res = 8U;
  uint32_t len11 = res;
  uint32_t pos11 = pos1 + len11;
  store64_be(input + pos11, x.v0);
  uint32_t res3 = 8U;
  uint32_t len20 = res3;
  uint32_t res4 = len11 + len20;
  uint32_t len21 = res4;
  return len10 + len21;
}

typedef struct raw_key_s
{
  u256 raw_key_k;
  uint16_t raw_key_significant_digits;
}
raw_key;

typedef struct raw_key__s
{
  u256 fst;
  uint16_t snd;
}
raw_key_;

static uint64_t raw_key_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos1 = u256_validator(input, pos);
  if (is_error(pos1))
    return pos1;
  else
    return significant_digits_t_validator(input, pos1);
}

static raw_key raw_key_reader(LowParse_Slice_slice input, uint32_t pos)
{
  u256 x1 = u256_reader(input, pos);
  uint32_t pos2 = u256_jumper(pos);
  uint16_t x2 = significant_digits_t_reader(input, pos2);
  raw_key_ res = { .fst = x1, .snd = x2 };
  u256 raw_key_k = res.fst;
  uint16_t raw_key_significant_digits = res.snd;
  return
    ((raw_key){ .raw_key_k = raw_key_k, .raw_key_significant_digits = raw_key_significant_digits });
}

static uint32_t raw_key_lserializer(raw_key x, uint8_t *input, uint32_t pos)
{
  uint32_t res = u256_lserializer(x.raw_key_k, input, pos);
  uint32_t len1 = res;
  uint32_t pos1 = pos + len1;
  uint32_t res0 = significant_digits_t_lserializer(x.raw_key_significant_digits, input, pos1);
  uint32_t len2 = res0;
  return len1 + len2;
}

#define Key_internal 0
#define Key_application 1

typedef uint8_t key_kind;

#define DValueNone 0
#define DValueSome 1

typedef uint8_t dvalue_kind;

#define V_payload_DValueNone 0
#define V_payload_DValueSome 1

typedef uint8_t application_record_v_payload_tags;

typedef struct application_record_v_payload_s
{
  application_record_v_payload_tags tag;
  Zeta_Steel_ApplicationTypes_value_type _0;
}
application_record_v_payload;

static uint32_t application_record_v_payload_size32(application_record_v_payload x)
{
  dvalue_kind tg;
  if (x.tag == V_payload_DValueNone)
    tg = DValueNone;
  else if (x.tag == V_payload_DValueSome)
    tg = DValueSome;
  else
    tg = KRML_EABORT(dvalue_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint32_t s1 = 1U;
  uint32_t s2;
  if (DValueNone == tg)
    s2 = 0U;
  else
  {
    Zeta_Steel_ApplicationTypes_value_type ite;
    if (x.tag == V_payload_DValueSome)
      ite = x._0;
    else
      ite =
        KRML_EABORT(Zeta_Steel_ApplicationTypes_value_type,
          "unreachable (pattern matches are exhaustive in F*)");
    s2 = application_value_size32(ite);
  }
  return s1 + s2;
}

static uint64_t
application_record_v_payload_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t len_after_tag;
  if ((uint64_t)input.len - pos < 1ULL)
    len_after_tag = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    len_after_tag = pos + 1ULL;
  if (is_error(len_after_tag))
    return len_after_tag;
  else
  {
    uint8_t k_ = input.base[(uint32_t)pos];
    if (k_ == 0U)
      if ((uint64_t)input.len - len_after_tag < 0ULL)
        return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        return len_after_tag + 0ULL;
    else if (k_ == 1U)
      return application_value_validator(input, len_after_tag);
    else
      return VALIDATOR_ERROR_GENERIC;
  }
}

static uint32_t application_record_v_payload_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + 1U;
  uint8_t k_ = input.base[pos];
  if (k_ == 0U)
    return pos_after_tag + 0U;
  else if (k_ == 1U)
    return application_value_jumper(input, pos_after_tag);
  else
    return 0U;
}

static application_record_v_payload
application_record_v_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  dvalue_kind k;
  if (res == 0U)
    k = DValueNone;
  else if (res == 1U)
    k = DValueSome;
  else
    k = DValueNone;
  uint32_t pos_ = pos + 1U;
  if (DValueNone == k)
    return ((application_record_v_payload){ .tag = V_payload_DValueNone });
  else
  {
    Zeta_Steel_ApplicationTypes_value_type res = application_value_reader(input, pos_);
    return ((application_record_v_payload){ .tag = V_payload_DValueSome, ._0 = res });
  }
}

static uint32_t
application_record_v_payload_lserializer(
  application_record_v_payload x,
  uint8_t *b,
  uint32_t pos
)
{
  dvalue_kind tg;
  if (x.tag == V_payload_DValueNone)
    tg = DValueNone;
  else if (x.tag == V_payload_DValueSome)
    tg = DValueSome;
  else
    tg = KRML_EABORT(dvalue_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t ite0;
  if (DValueNone == tg)
    ite0 = 0U;
  else
    ite0 = 1U;
  b[pos] = ite0;
  uint32_t len = 1U;
  uint32_t res0 = pos + len;
  uint32_t pos_ = res0;
  uint32_t pos_0 = pos_;
  uint32_t res1 = pos_0 - pos;
  uint32_t len1 = res1;
  uint32_t pos1 = pos + len1;
  uint32_t res;
  if (DValueNone == tg)
    res = 0U;
  else
  {
    Zeta_Steel_ApplicationTypes_value_type ite;
    if (x.tag == V_payload_DValueSome)
      ite = x._0;
    else
      ite =
        KRML_EABORT(Zeta_Steel_ApplicationTypes_value_type,
          "unreachable (pattern matches are exhaustive in F*)");
    res = application_value_lserializer(ite, b, pos1);
  }
  uint32_t len2 = res;
  return len1 + len2;
}

typedef struct application_record_s
{
  Zeta_Steel_ApplicationTypes_key_type ar_key;
  application_record_v_payload v_payload;
}
application_record;

typedef struct application_record__s
{
  Zeta_Steel_ApplicationTypes_key_type fst;
  application_record_v_payload snd;
}
application_record_;

static uint32_t application_record_size32(application_record input)
{
  uint32_t v1 = application_key_size32(input.ar_key);
  uint32_t v2 = application_record_v_payload_size32(input.v_payload);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t application_record_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos1 = application_key_validator(input, pos);
  if (is_error(pos1))
    return pos1;
  else
    return application_record_v_payload_validator(input, pos1);
}

static uint32_t application_record_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return application_record_v_payload_jumper(input, application_key_jumper(input, pos));
}

static application_record application_record_reader(LowParse_Slice_slice input, uint32_t pos)
{
  Zeta_Steel_ApplicationTypes_key_type x1 = application_key_reader(input, pos);
  uint32_t pos2 = application_key_jumper(input, pos);
  application_record_v_payload x2 = application_record_v_payload_reader(input, pos2);
  application_record_ res = { .fst = x1, .snd = x2 };
  Zeta_Steel_ApplicationTypes_key_type ar_key = res.fst;
  application_record_v_payload v_payload = res.snd;
  return ((application_record){ .ar_key = ar_key, .v_payload = v_payload });
}

static uint32_t
application_record_lserializer(application_record x, uint8_t *input, uint32_t pos)
{
  uint32_t res = application_key_lserializer(x.ar_key, input, pos);
  uint32_t len1 = res;
  uint32_t pos1 = pos + len1;
  uint32_t res0 = application_record_v_payload_lserializer(x.v_payload, input, pos1);
  uint32_t len2 = res0;
  return len1 + len2;
}

#define Vnone 0
#define Vsome 1

typedef uint8_t voption;

#define Vfalse 0
#define Vtrue 1

typedef uint8_t vbool;

static uint32_t vbool_size32(vbool x)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return 1U;
}

static uint64_t vbool_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t res;
  if ((uint64_t)input.len - pos < 1ULL)
    res = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    res = pos + 1ULL;
  if (is_error(res))
    return res;
  else
  {
    uint8_t va = input.base[(uint32_t)pos];
    bool ite;
    if (va == 0U)
      ite = true;
    else if (va == 1U)
      ite = true;
    else
      ite = false;
    if (!ite)
      return VALIDATOR_ERROR_GENERIC;
    else
      return res;
  }
}

static vbool vbool_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  if (res == 0U)
    return Vfalse;
  else if (res == 1U)
    return Vtrue;
  else
    return Vfalse;
}

static uint32_t vbool_writer(vbool x, LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t ite;
  if (Vfalse == x)
    ite = 0U;
  else
    ite = 1U;
  input.base[pos] = ite;
  uint32_t len = 1U;
  uint32_t res = pos + len;
  uint32_t pos_ = res;
  uint32_t pos_0 = pos_;
  return pos_0;
}

static uint32_t vbool_lserializer(vbool x, uint8_t *b, uint32_t pos)
{
  uint32_t pos_ = vbool_writer(x, ((LowParse_Slice_slice){ .base = b, .len = pos + 1U }), pos);
  return pos_ - pos;
}

static uint32_t (*hash_value_size32)(u256 x0) = u256_size32;

static uint64_t hash_value_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 32ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 32ULL;
}

static uint32_t hash_value_jumper(uint32_t pos)
{
  return pos + 32U;
}

static u256 (*hash_value_reader)(LowParse_Slice_slice x0, uint32_t x1) = u256_reader;

static uint32_t
(*hash_value_lserializer)(u256 x0, uint8_t *x1, uint32_t x2) = u256_lserializer;

static Zeta_Steel_KeyUtils_u256 synth_u256(u256 x)
{
  return ((Zeta_Steel_KeyUtils_u256){ .v3 = x.v3, .v2 = x.v2, .v1 = x.v1, .v0 = x.v0 });
}

static u256 synth_u256_recip(Zeta_Steel_KeyUtils_u256 x)
{
  uint64_t v3 = x.v3;
  uint64_t v2 = x.v2;
  uint64_t v1 = x.v1;
  uint64_t v0 = x.v0;
  return ((u256){ .v3 = v3, .v2 = v2, .v1 = v1, .v0 = v0 });
}

static Zeta_Steel_KeyUtils_raw_key synth_raw_key(raw_key x)
{
  return
    (
      (Zeta_Steel_KeyUtils_raw_key){
        .k = synth_u256(x.raw_key_k),
        .significant_digits = x.raw_key_significant_digits
      }
    );
}

static raw_key synth_raw_key_recip(Zeta_Steel_KeyUtils_raw_key x)
{
  return
    (
      (raw_key){
        .raw_key_k = synth_u256_recip(x.k),
        .raw_key_significant_digits = x.significant_digits
      }
    );
}

static uint32_t base_key_size32(Zeta_Steel_KeyUtils_raw_key x)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return 34U;
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

static uint64_t base_key_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t res = raw_key_validator(input, pos);
  if (is_error(res))
    return res;
  else
  {
    raw_key va = raw_key_reader(input, (uint32_t)pos);
    Zeta_Steel_KeyUtils_raw_key
    r_ = truncate_key(synth_raw_key(va), synth_raw_key(va).significant_digits);
    if (!__eq__Zeta_Steel_KeyUtils_raw_key(r_, synth_raw_key(va)))
      return VALIDATOR_ERROR_GENERIC;
    else
      return res;
  }
}

static uint32_t base_key_jumper(uint32_t pos)
{
  return pos + 34U;
}

static Zeta_Steel_KeyUtils_raw_key base_key_reader(LowParse_Slice_slice input, uint32_t pos)
{
  raw_key res = raw_key_reader(input, pos);
  return synth_raw_key(res);
}

static uint32_t
base_key_lserializer(Zeta_Steel_KeyUtils_raw_key x, uint8_t *input, uint32_t pos)
{
  return raw_key_lserializer(synth_raw_key_recip(x), input, pos);
}

typedef struct descendent_hash_desc_s
{
  Zeta_Steel_KeyUtils_raw_key dhd_key;
  u256 dhd_h;
  vbool evicted_to_blum;
}
descendent_hash_desc;

typedef struct __Zeta_Steel_KeyUtils_raw_key_Zeta_Formats_Aux_U256_u256_s
{
  Zeta_Steel_KeyUtils_raw_key fst;
  u256 snd;
}
__Zeta_Steel_KeyUtils_raw_key_Zeta_Formats_Aux_U256_u256;

typedef struct descendent_hash_desc__s
{
  __Zeta_Steel_KeyUtils_raw_key_Zeta_Formats_Aux_U256_u256 fst;
  vbool snd;
}
descendent_hash_desc_;

static uint32_t descendent_hash_desc_size32(descendent_hash_desc input)
{
  uint32_t v10 = base_key_size32(input.dhd_key);
  uint32_t v20 = hash_value_size32(input.dhd_h);
  uint32_t v1;
  if (4294967295U - v20 < v10)
    v1 = 4294967295U;
  else
    v1 = v10 + v20;
  uint32_t v2 = vbool_size32(input.evicted_to_blum);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t descendent_hash_desc_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos10 = base_key_validator(input, pos);
  uint64_t pos1;
  if (is_error(pos10))
    pos1 = pos10;
  else
    pos1 = hash_value_validator(input, pos10);
  if (is_error(pos1))
    return pos1;
  else
    return vbool_validator(input, pos1);
}

static uint32_t descendent_hash_desc_jumper(uint32_t pos)
{
  return pos + 67U;
}

static descendent_hash_desc
descendent_hash_desc_reader(LowParse_Slice_slice input, uint32_t pos)
{
  Zeta_Steel_KeyUtils_raw_key x1 = base_key_reader(input, pos);
  uint32_t pos20 = base_key_jumper(pos);
  u256 x2 = hash_value_reader(input, pos20);
  __Zeta_Steel_KeyUtils_raw_key_Zeta_Formats_Aux_U256_u256 x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = hash_value_jumper(base_key_jumper(pos));
  vbool x20 = vbool_reader(input, pos2);
  descendent_hash_desc_ res = { .fst = x10, .snd = x20 };
  vbool evicted_to_blum = res.snd;
  u256 dhd_h = res.fst.snd;
  Zeta_Steel_KeyUtils_raw_key dhd_key = res.fst.fst;
  return
    (
      (descendent_hash_desc){
        .dhd_key = dhd_key,
        .dhd_h = dhd_h,
        .evicted_to_blum = evicted_to_blum
      }
    );
}

static uint32_t
descendent_hash_desc_lserializer(descendent_hash_desc x, uint8_t *input, uint32_t pos)
{
  uint32_t res = base_key_lserializer(x.dhd_key, input, pos);
  uint32_t len1 = res;
  uint32_t pos10 = pos + len1;
  uint32_t res0 = hash_value_lserializer(x.dhd_h, input, pos10);
  uint32_t len2 = res0;
  uint32_t res1 = len1 + len2;
  uint32_t len10 = res1;
  uint32_t pos1 = pos + len10;
  uint32_t res2 = vbool_lserializer(x.evicted_to_blum, input, pos1);
  uint32_t len20 = res2;
  return len10 + len20;
}

#define Dh_vnone 0
#define Dh_vsome 1

typedef uint8_t descendent_hash_tags;

typedef struct descendent_hash_s
{
  descendent_hash_tags tag;
  descendent_hash_desc _0;
}
descendent_hash;

static uint32_t descendent_hash_size32(descendent_hash x)
{
  voption tg;
  if (x.tag == Dh_vnone)
    tg = Vnone;
  else if (x.tag == Dh_vsome)
    tg = Vsome;
  else
    tg = KRML_EABORT(voption, "unreachable (pattern matches are exhaustive in F*)");
  uint32_t s1 = 1U;
  uint32_t s2;
  if (Vnone == tg)
    s2 = 0U;
  else
  {
    descendent_hash_desc ite;
    if (x.tag == Dh_vsome)
      ite = x._0;
    else
      ite = KRML_EABORT(descendent_hash_desc, "unreachable (pattern matches are exhaustive in F*)");
    s2 = descendent_hash_desc_size32(ite);
  }
  return s1 + s2;
}

static uint64_t descendent_hash_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t len_after_tag;
  if ((uint64_t)input.len - pos < 1ULL)
    len_after_tag = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    len_after_tag = pos + 1ULL;
  if (is_error(len_after_tag))
    return len_after_tag;
  else
  {
    uint8_t k_ = input.base[(uint32_t)pos];
    if (k_ == 0U)
      if ((uint64_t)input.len - len_after_tag < 0ULL)
        return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        return len_after_tag + 0ULL;
    else if (k_ == 1U)
      return descendent_hash_desc_validator(input, len_after_tag);
    else
      return VALIDATOR_ERROR_GENERIC;
  }
}

static uint32_t descendent_hash_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + 1U;
  uint8_t k_ = input.base[pos];
  if (k_ == 0U)
    return pos_after_tag + 0U;
  else if (k_ == 1U)
    return descendent_hash_desc_jumper(pos_after_tag);
  else
    return 0U;
}

static descendent_hash descendent_hash_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  voption k;
  if (res == 0U)
    k = Vnone;
  else if (res == 1U)
    k = Vsome;
  else
    k = Vnone;
  uint32_t pos_ = pos + 1U;
  if (Vnone == k)
    return ((descendent_hash){ .tag = Dh_vnone });
  else
  {
    descendent_hash_desc res = descendent_hash_desc_reader(input, pos_);
    return ((descendent_hash){ .tag = Dh_vsome, ._0 = res });
  }
}

static uint32_t descendent_hash_lserializer(descendent_hash x, uint8_t *b, uint32_t pos)
{
  voption tg;
  if (x.tag == Dh_vnone)
    tg = Vnone;
  else if (x.tag == Dh_vsome)
    tg = Vsome;
  else
    tg = KRML_EABORT(voption, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t ite0;
  if (Vnone == tg)
    ite0 = 0U;
  else
    ite0 = 1U;
  b[pos] = ite0;
  uint32_t len = 1U;
  uint32_t res0 = pos + len;
  uint32_t pos_ = res0;
  uint32_t pos_0 = pos_;
  uint32_t res1 = pos_0 - pos;
  uint32_t len1 = res1;
  uint32_t pos1 = pos + len1;
  uint32_t res;
  if (Vnone == tg)
    res = 0U;
  else
  {
    descendent_hash_desc ite;
    if (x.tag == Dh_vsome)
      ite = x._0;
    else
      ite = KRML_EABORT(descendent_hash_desc, "unreachable (pattern matches are exhaustive in F*)");
    res = descendent_hash_desc_lserializer(ite, b, pos1);
  }
  uint32_t len2 = res;
  return len1 + len2;
}

typedef struct mval_value_s
{
  descendent_hash l;
  descendent_hash r;
}
mval_value;

typedef struct mval_value__s
{
  descendent_hash fst;
  descendent_hash snd;
}
mval_value_;

static uint32_t mval_value_size32(mval_value input)
{
  uint32_t v1 = descendent_hash_size32(input.l);
  uint32_t v2 = descendent_hash_size32(input.r);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t mval_value_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos1 = descendent_hash_validator(input, pos);
  if (is_error(pos1))
    return pos1;
  else
    return descendent_hash_validator(input, pos1);
}

static uint32_t mval_value_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return descendent_hash_jumper(input, descendent_hash_jumper(input, pos));
}

static mval_value mval_value_reader(LowParse_Slice_slice input, uint32_t pos)
{
  descendent_hash x1 = descendent_hash_reader(input, pos);
  uint32_t pos2 = descendent_hash_jumper(input, pos);
  descendent_hash x2 = descendent_hash_reader(input, pos2);
  mval_value_ res = { .fst = x1, .snd = x2 };
  descendent_hash l = res.fst;
  descendent_hash r = res.snd;
  return ((mval_value){ .l = l, .r = r });
}

static uint32_t mval_value_lserializer(mval_value x, uint8_t *input, uint32_t pos)
{
  uint32_t res = descendent_hash_lserializer(x.l, input, pos);
  uint32_t len1 = res;
  uint32_t pos1 = pos + len1;
  uint32_t res0 = descendent_hash_lserializer(x.r, input, pos1);
  uint32_t len2 = res0;
  return len1 + len2;
}

static uint32_t internal_key_size32(Zeta_Steel_KeyUtils_raw_key input)
{
  return base_key_size32(input);
}

static uint64_t internal_key_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t res = base_key_validator(input, pos);
  if (is_error(res))
    return res;
  else
  {
    Zeta_Steel_KeyUtils_raw_key bk = base_key_reader(input, (uint32_t)pos);
    if (is_internal_key(bk))
      return res;
    else
      return VALIDATOR_ERROR_GENERIC;
  }
}

static uint32_t internal_key_jumper(uint32_t pos)
{
  return pos + 34U;
}

static Zeta_Steel_KeyUtils_raw_key
internal_key_reader(LowParse_Slice_slice input, uint32_t pos)
{
  Zeta_Steel_KeyUtils_raw_key res = base_key_reader(input, pos);
  return res;
}

static uint32_t
internal_key_lserializer(Zeta_Steel_KeyUtils_raw_key x, uint8_t *input, uint32_t pos)
{
  return base_key_lserializer(x, input, pos);
}

typedef struct internal_record_s
{
  Zeta_Steel_KeyUtils_raw_key ir_key;
  mval_value ir_value;
}
internal_record;

typedef struct internal_record__s
{
  Zeta_Steel_KeyUtils_raw_key fst;
  mval_value snd;
}
internal_record_;

static uint32_t internal_record_size32(internal_record input)
{
  uint32_t v1 = internal_key_size32(input.ir_key);
  uint32_t v2 = mval_value_size32(input.ir_value);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t internal_record_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos1 = internal_key_validator(input, pos);
  if (is_error(pos1))
    return pos1;
  else
    return mval_value_validator(input, pos1);
}

static uint32_t internal_record_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return mval_value_jumper(input, internal_key_jumper(pos));
}

static internal_record internal_record_reader(LowParse_Slice_slice input, uint32_t pos)
{
  Zeta_Steel_KeyUtils_raw_key x1 = internal_key_reader(input, pos);
  uint32_t pos2 = internal_key_jumper(pos);
  mval_value x2 = mval_value_reader(input, pos2);
  internal_record_ res = { .fst = x1, .snd = x2 };
  Zeta_Steel_KeyUtils_raw_key ir_key = res.fst;
  mval_value ir_value = res.snd;
  return ((internal_record){ .ir_key = ir_key, .ir_value = ir_value });
}

static uint32_t internal_record_lserializer(internal_record x, uint8_t *input, uint32_t pos)
{
  uint32_t res = internal_key_lserializer(x.ir_key, input, pos);
  uint32_t len1 = res;
  uint32_t pos1 = pos + len1;
  uint32_t res0 = mval_value_lserializer(x.ir_value, input, pos1);
  uint32_t len2 = res0;
  return len1 + len2;
}

#define Record_kv_key_internal 0
#define Record_kv_key_application 1

typedef uint8_t record_tags;

typedef struct record_s
{
  record_tags tag;
  union {
    internal_record case_Record_kv_key_internal;
    application_record case_Record_kv_key_application;
  }
  ;
}
record;

static uint32_t record_size32(record x)
{
  key_kind tg;
  if (x.tag == Record_kv_key_internal)
    tg = Key_internal;
  else if (x.tag == Record_kv_key_application)
    tg = Key_application;
  else
    tg = KRML_EABORT(key_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint32_t s1 = 1U;
  uint32_t s2;
  if (Key_internal == tg)
  {
    internal_record ite;
    if (x.tag == Record_kv_key_internal)
      ite = x.case_Record_kv_key_internal;
    else
      ite = KRML_EABORT(internal_record, "unreachable (pattern matches are exhaustive in F*)");
    s2 = internal_record_size32(ite);
  }
  else
  {
    application_record ite;
    if (x.tag == Record_kv_key_application)
      ite = x.case_Record_kv_key_application;
    else
      ite = KRML_EABORT(application_record, "unreachable (pattern matches are exhaustive in F*)");
    s2 = application_record_size32(ite);
  }
  return s1 + s2;
}

static uint64_t record_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t len_after_tag;
  if ((uint64_t)input.len - pos < 1ULL)
    len_after_tag = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    len_after_tag = pos + 1ULL;
  if (is_error(len_after_tag))
    return len_after_tag;
  else
  {
    uint8_t k_ = input.base[(uint32_t)pos];
    if (k_ == 0U)
      return internal_record_validator(input, len_after_tag);
    else if (k_ == 1U)
      return application_record_validator(input, len_after_tag);
    else
      return VALIDATOR_ERROR_GENERIC;
  }
}

static uint32_t record_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + 1U;
  uint8_t k_ = input.base[pos];
  if (k_ == 0U)
    return internal_record_jumper(input, pos_after_tag);
  else if (k_ == 1U)
    return application_record_jumper(input, pos_after_tag);
  else
    return 0U;
}

static record record_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  key_kind k;
  if (res == 0U)
    k = Key_internal;
  else if (res == 1U)
    k = Key_application;
  else
    k = Key_internal;
  uint32_t pos_ = pos + 1U;
  if (Key_internal == k)
  {
    internal_record res = internal_record_reader(input, pos_);
    return ((record){ .tag = Record_kv_key_internal, { .case_Record_kv_key_internal = res } });
  }
  else
  {
    application_record res = application_record_reader(input, pos_);
    return
      ((record){ .tag = Record_kv_key_application, { .case_Record_kv_key_application = res } });
  }
}

static uint32_t record_lserializer(record x, uint8_t *b, uint32_t pos)
{
  key_kind tg;
  if (x.tag == Record_kv_key_internal)
    tg = Key_internal;
  else if (x.tag == Record_kv_key_application)
    tg = Key_application;
  else
    tg = KRML_EABORT(key_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t ite0;
  if (Key_internal == tg)
    ite0 = 0U;
  else
    ite0 = 1U;
  b[pos] = ite0;
  uint32_t len = 1U;
  uint32_t res0 = pos + len;
  uint32_t pos_ = res0;
  uint32_t pos_0 = pos_;
  uint32_t res1 = pos_0 - pos;
  uint32_t len1 = res1;
  uint32_t pos1 = pos + len1;
  uint32_t res;
  if (Key_internal == tg)
  {
    internal_record ite;
    if (x.tag == Record_kv_key_internal)
      ite = x.case_Record_kv_key_internal;
    else
      ite = KRML_EABORT(internal_record, "unreachable (pattern matches are exhaustive in F*)");
    res = internal_record_lserializer(ite, b, pos1);
  }
  else
  {
    application_record ite;
    if (x.tag == Record_kv_key_application)
      ite = x.case_Record_kv_key_application;
    else
      ite = KRML_EABORT(application_record, "unreachable (pattern matches are exhaustive in F*)");
    res = application_record_lserializer(ite, b, pos1);
  }
  uint32_t len2 = res;
  return len1 + len2;
}

typedef struct addm_payload_s
{
  record addm_r;
  uint16_t addm_s;
  uint16_t addm_s2;
}
addm_payload;

typedef struct __Zeta_Formats_Aux_Record_record_uint16_t_s
{
  record fst;
  uint16_t snd;
}
__Zeta_Formats_Aux_Record_record_uint16_t;

typedef struct addm_payload__s
{
  __Zeta_Formats_Aux_Record_record_uint16_t fst;
  uint16_t snd;
}
addm_payload_;

static uint32_t addm_payload_size32(addm_payload input)
{
  uint32_t v10 = record_size32(input.addm_r);
  uint32_t v20 = slot_id_size32(input.addm_s);
  uint32_t v1;
  if (4294967295U - v20 < v10)
    v1 = 4294967295U;
  else
    v1 = v10 + v20;
  uint32_t v2 = slot_id_size32(input.addm_s2);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t addm_payload_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos10 = record_validator(input, pos);
  uint64_t pos1;
  if (is_error(pos10))
    pos1 = pos10;
  else
    pos1 = slot_id_validator(input, pos10);
  if (is_error(pos1))
    return pos1;
  else
    return slot_id_validator(input, pos1);
}

static uint32_t addm_payload_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return slot_id_jumper(slot_id_jumper(record_jumper(input, pos)));
}

static addm_payload addm_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  record x1 = record_reader(input, pos);
  uint32_t pos20 = record_jumper(input, pos);
  uint16_t x2 = slot_id_reader(input, pos20);
  __Zeta_Formats_Aux_Record_record_uint16_t x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = slot_id_jumper(record_jumper(input, pos));
  uint16_t x20 = slot_id_reader(input, pos2);
  addm_payload_ res = { .fst = x10, .snd = x20 };
  uint16_t addm_s2 = res.snd;
  uint16_t addm_s = res.fst.snd;
  record addm_r = res.fst.fst;
  return ((addm_payload){ .addm_r = addm_r, .addm_s = addm_s, .addm_s2 = addm_s2 });
}

typedef struct evictm_payload_s
{
  uint16_t evictm_s;
  uint16_t evictm_s2;
}
evictm_payload;

static uint32_t evictm_payload_size32(evictm_payload input)
{
  uint32_t v1 = slot_id_size32(input.evictm_s);
  uint32_t v2 = slot_id_size32(input.evictm_s2);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t evictm_payload_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 4ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 4ULL;
}

static uint32_t evictm_payload_jumper(uint32_t pos)
{
  return pos + 4U;
}

static evictm_payload evictm_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint16_t x1 = slot_id_reader(input, pos);
  uint32_t pos2 = slot_id_jumper(pos);
  uint16_t x2 = slot_id_reader(input, pos2);
  __uint16_t_uint16_t res = { .fst = x1, .snd = x2 };
  uint16_t evictm_s = res.fst;
  uint16_t evictm_s2 = res.snd;
  return ((evictm_payload){ .evictm_s = evictm_s, .evictm_s2 = evictm_s2 });
}

static uint32_t runapp_payload_hdr_size32(uint8_t x)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return 1U;
}

static uint64_t runapp_payload_hdr_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 1ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 1ULL;
}

static uint32_t runapp_payload_hdr_jumper(uint32_t pos)
{
  return pos + 1U;
}

static uint8_t runapp_payload_hdr_reader(LowParse_Slice_slice sl, uint32_t pos)
{
  return sl.base[pos];
}

static uint32_t thread_id_size32(uint16_t x)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return 2U;
}

static uint64_t thread_id_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 2ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 2ULL;
}

static uint32_t thread_id_jumper(uint32_t pos)
{
  return pos + 2U;
}

static uint16_t thread_id_reader(LowParse_Slice_slice sl, uint32_t pos)
{
  return load16_be(sl.base + pos);
}

static uint32_t thread_id_lserializer(uint16_t v, uint8_t *b, uint32_t pos)
{
  store16_be(b + pos, v);
  return 2U;
}

typedef struct stamped_record_s
{
  record sr_record;
  timestamp sr_timestamp;
  uint16_t sr_thread_id;
}
stamped_record;

static uint32_t stamped_record_lserializer(stamped_record x, uint8_t *input, uint32_t pos)
{
  uint32_t res = record_lserializer(x.sr_record, input, pos);
  uint32_t len1 = res;
  uint32_t pos10 = pos + len1;
  uint32_t res0 = timestamp_lserializer(x.sr_timestamp, input, pos10);
  uint32_t len2 = res0;
  uint32_t res1 = len1 + len2;
  uint32_t len10 = res1;
  uint32_t pos1 = pos + len10;
  uint32_t res2 = thread_id_lserializer(x.sr_thread_id, input, pos1);
  uint32_t len20 = res2;
  return len10 + len20;
}

#define MV 0
#define DVNone 1
#define DVSome 2

typedef uint8_t value_kind;

#define Value_payload_MV 0
#define Value_payload_DVNone 1
#define Value_payload_DVSome 2

typedef uint8_t value_tags;

typedef struct value_s
{
  value_tags tag;
  union {
    mval_value case_Value_payload_MV;
    Zeta_Steel_ApplicationTypes_value_type case_Value_payload_DVSome;
  }
  ;
}
value;

static uint32_t value_lserializer(value x, uint8_t *b, uint32_t pos)
{
  value_kind tg;
  if (x.tag == Value_payload_MV)
    tg = MV;
  else if (x.tag == Value_payload_DVNone)
    tg = DVNone;
  else if (x.tag == Value_payload_DVSome)
    tg = DVSome;
  else
    tg = KRML_EABORT(value_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t ite0;
  if (MV == tg)
    ite0 = 0U;
  else if (DVNone == tg)
    ite0 = 1U;
  else
    ite0 = 2U;
  b[pos] = ite0;
  uint32_t len = 1U;
  uint32_t res0 = pos + len;
  uint32_t pos_ = res0;
  uint32_t pos_0 = pos_;
  uint32_t res1 = pos_0 - pos;
  uint32_t len1 = res1;
  uint32_t pos1 = pos + len1;
  uint32_t res;
  if (MV == tg)
  {
    mval_value ite;
    if (x.tag == Value_payload_MV)
      ite = x.case_Value_payload_MV;
    else
      ite = KRML_EABORT(mval_value, "unreachable (pattern matches are exhaustive in F*)");
    res = mval_value_lserializer(ite, b, pos1);
  }
  else if (DVNone == tg)
    res = 0U;
  else
  {
    Zeta_Steel_ApplicationTypes_value_type ite;
    if (x.tag == Value_payload_DVSome)
      ite = x.case_Value_payload_DVSome;
    else
      ite =
        KRML_EABORT(Zeta_Steel_ApplicationTypes_value_type,
          "unreachable (pattern matches are exhaustive in F*)");
    res = application_value_lserializer(ite, b, pos1);
  }
  uint32_t len2 = res;
  return len1 + len2;
}

static Zeta_Steel_KeyUtils_u256 synth_hash_value(u256 x)
{
  return synth_u256(x);
}

static u256 synth_hash_value_recip(Zeta_Steel_KeyUtils_u256 x)
{
  return synth_u256_recip(x);
}

static Zeta_Steel_LogEntry_Types_vbool synth_vbool(vbool x)
{
  switch (x)
  {
    case Vfalse:
      {
        return Zeta_Steel_LogEntry_Types_Vfalse;
      }
    case Vtrue:
      {
        return Zeta_Steel_LogEntry_Types_Vtrue;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static vbool synth_vbool_recip(Zeta_Steel_LogEntry_Types_vbool x)
{
  switch (x)
  {
    case Zeta_Steel_LogEntry_Types_Vfalse:
      {
        return Vfalse;
      }
    case Zeta_Steel_LogEntry_Types_Vtrue:
      {
        return Vtrue;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static Zeta_Steel_LogEntry_Types_descendent_hash_desc
synth_descendent_hash_desc(descendent_hash_desc x)
{
  return
    (
      (Zeta_Steel_LogEntry_Types_descendent_hash_desc){
        .dhd_key = x.dhd_key,
        .dhd_h = synth_hash_value(x.dhd_h),
        .evicted_to_blum = synth_vbool(x.evicted_to_blum)
      }
    );
}

static descendent_hash_desc
synth_descendent_hash_desc_recip(Zeta_Steel_LogEntry_Types_descendent_hash_desc x)
{
  return
    (
      (descendent_hash_desc){
        .dhd_key = x.dhd_key,
        .dhd_h = synth_hash_value_recip(x.dhd_h),
        .evicted_to_blum = synth_vbool_recip(x.evicted_to_blum)
      }
    );
}

static Zeta_Steel_LogEntry_Types_descendent_hash synth_descendent_hash(descendent_hash x)
{
  if (x.tag == Dh_vnone)
    return
      ((Zeta_Steel_LogEntry_Types_descendent_hash){ .tag = Zeta_Steel_LogEntry_Types_Dh_vnone });
  else if (x.tag == Dh_vsome)
  {
    descendent_hash_desc d = x._0;
    return
      (
        (Zeta_Steel_LogEntry_Types_descendent_hash){
          .tag = Zeta_Steel_LogEntry_Types_Dh_vsome,
          ._0 = synth_descendent_hash_desc(d)
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

static descendent_hash synth_descendent_hash_recip(Zeta_Steel_LogEntry_Types_descendent_hash x)
{
  if (x.tag == Zeta_Steel_LogEntry_Types_Dh_vnone)
    return ((descendent_hash){ .tag = Dh_vnone });
  else if (x.tag == Zeta_Steel_LogEntry_Types_Dh_vsome)
  {
    Zeta_Steel_LogEntry_Types_descendent_hash_desc d = x._0;
    return ((descendent_hash){ .tag = Dh_vsome, ._0 = synth_descendent_hash_desc_recip(d) });
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

static Zeta_Steel_LogEntry_Types_mval_value synth_mval_value(mval_value x)
{
  return
    (
      (Zeta_Steel_LogEntry_Types_mval_value){
        .l = synth_descendent_hash(x.l),
        .r = synth_descendent_hash(x.r)
      }
    );
}

static mval_value synth_mval_value_recip(Zeta_Steel_LogEntry_Types_mval_value x)
{
  Zeta_Steel_LogEntry_Types_descendent_hash l = x.l;
  Zeta_Steel_LogEntry_Types_descendent_hash r = x.r;
  return
    ((mval_value){ .l = synth_descendent_hash_recip(l), .r = synth_descendent_hash_recip(r) });
}

static Zeta_Steel_LogEntry_Types_record synth_record(record x)
{
  if (x.tag == Record_kv_key_internal)
  {
    internal_record r = x.case_Record_kv_key_internal;
    return
      (
        (Zeta_Steel_LogEntry_Types_record){
          .fst = { .tag = Zeta_Steel_LogEntry_Types_InternalKey, { .case_InternalKey = r.ir_key } },
          .snd = {
            .tag = Zeta_Steel_LogEntry_Types_MValue,
            { .case_MValue = synth_mval_value(r.ir_value) }
          }
        }
      );
  }
  else if (x.tag == Record_kv_key_application)
  {
    application_record r = x.case_Record_kv_key_application;
    FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type ite;
    if (r.v_payload.tag == V_payload_DValueNone)
      ite =
        (
          (FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else if (r.v_payload.tag == V_payload_DValueSome)
    {
      Zeta_Steel_ApplicationTypes_value_type v = r.v_payload._0;
      ite =
        (
          (FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type){
            .tag = FStar_Pervasives_Native_Some,
            .v = v
          }
        );
    }
    else
      ite =
        KRML_EABORT(FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type,
          "unreachable (pattern matches are exhaustive in F*)");
    return
      (
        (Zeta_Steel_LogEntry_Types_record){
          .fst = {
            .tag = Zeta_Steel_LogEntry_Types_ApplicationKey,
            { .case_ApplicationKey = r.ar_key }
          },
          .snd = { .tag = Zeta_Steel_LogEntry_Types_DValue, { .case_DValue = ite } }
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

static record synth_record_recip(Zeta_Steel_LogEntry_Types_record x)
{
  Zeta_Steel_LogEntry_Types_key k = x.fst;
  Zeta_Steel_LogEntry_Types_value v = x.snd;
  if (k.tag == Zeta_Steel_LogEntry_Types_InternalKey)
  {
    Zeta_Steel_KeyUtils_raw_key ik = k.case_InternalKey;
    if (v.tag == Zeta_Steel_LogEntry_Types_MValue)
    {
      Zeta_Steel_LogEntry_Types_mval_value iv = v.case_MValue;
      return
        (
          (record){
            .tag = Record_kv_key_internal,
            {
              .case_Record_kv_key_internal = {
                .ir_key = ik,
                .ir_value = synth_mval_value_recip(iv)
              }
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
  else if (k.tag == Zeta_Steel_LogEntry_Types_ApplicationKey)
  {
    Zeta_Steel_ApplicationTypes_key_type ak = k.case_ApplicationKey;
    if (v.tag == Zeta_Steel_LogEntry_Types_DValue)
    {
      FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type dv = v.case_DValue;
      application_record_v_payload vp;
      if (dv.tag == FStar_Pervasives_Native_None)
        vp = ((application_record_v_payload){ .tag = V_payload_DValueNone });
      else if (dv.tag == FStar_Pervasives_Native_Some)
      {
        Zeta_Steel_ApplicationTypes_value_type v1 = dv.v;
        vp = ((application_record_v_payload){ .tag = V_payload_DValueSome, ._0 = v1 });
      }
      else
        vp =
          KRML_EABORT(application_record_v_payload,
            "unreachable (pattern matches are exhaustive in F*)");
      return
        (
          (record){
            .tag = Record_kv_key_application,
            { .case_Record_kv_key_application = { .ar_key = ak, .v_payload = vp } }
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

static value synth_value_recip(Zeta_Steel_LogEntry_Types_value x)
{
  if (x.tag == Zeta_Steel_LogEntry_Types_MValue)
  {
    Zeta_Steel_LogEntry_Types_mval_value v = x.case_MValue;
    return
      ((value){ .tag = Value_payload_MV, { .case_Value_payload_MV = synth_mval_value_recip(v) } });
  }
  else if
  (
    x.tag
    == Zeta_Steel_LogEntry_Types_DValue
    && x.case_DValue.tag == FStar_Pervasives_Native_None
  )
    return ((value){ .tag = Value_payload_DVNone });
  else if
  (
    x.tag
    == Zeta_Steel_LogEntry_Types_DValue
    && x.case_DValue.tag == FStar_Pervasives_Native_Some
  )
  {
    Zeta_Steel_ApplicationTypes_value_type v = x.case_DValue.v;
    return ((value){ .tag = Value_payload_DVSome, { .case_Value_payload_DVSome = v } });
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

static Zeta_Steel_LogEntry_Types_timestamp synth_timestamp(timestamp x)
{
  return ((Zeta_Steel_LogEntry_Types_timestamp){ .epoch = x.epoch, .counter = x.counter });
}

static timestamp synth_timestamp_recip(Zeta_Steel_LogEntry_Types_timestamp x)
{
  return ((timestamp){ .epoch = x.epoch, .counter = x.counter });
}

typedef struct evictb_payload_s
{
  uint16_t evictb_s;
  timestamp evictb_t;
}
evictb_payload;

typedef struct evictb_payload__s
{
  uint16_t fst;
  timestamp snd;
}
evictb_payload_;

static uint32_t evictb_payload_size32(evictb_payload input)
{
  uint32_t v1 = slot_id_size32(input.evictb_s);
  uint32_t v2 = timestamp_size32(input.evictb_t);
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t evictb_payload_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < 10ULL)
    return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + 10ULL;
}

static uint32_t evictb_payload_jumper(uint32_t pos)
{
  return pos + 10U;
}

static evictb_payload evictb_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint16_t x1 = slot_id_reader(input, pos);
  uint32_t pos2 = slot_id_jumper(pos);
  timestamp x2 = timestamp_reader(input, pos2);
  evictb_payload_ res = { .fst = x1, .snd = x2 };
  uint16_t evictb_s = res.fst;
  timestamp evictb_t = res.snd;
  return ((evictb_payload){ .evictb_s = evictb_s, .evictb_t = evictb_t });
}

typedef struct addb_payload_s
{
  record addb_r;
  uint16_t addb_s;
  timestamp addb_t;
  uint16_t addb_tid;
}
addb_payload;

typedef struct __Zeta_Formats_Aux_Timestamp_timestamp_uint16_t_s
{
  timestamp fst;
  uint16_t snd;
}
__Zeta_Formats_Aux_Timestamp_timestamp_uint16_t;

typedef struct addb_payload__s
{
  __Zeta_Formats_Aux_Record_record_uint16_t fst;
  __Zeta_Formats_Aux_Timestamp_timestamp_uint16_t snd;
}
addb_payload_;

static uint32_t addb_payload_size32(addb_payload input)
{
  uint32_t v10 = record_size32(input.addb_r);
  uint32_t v20 = slot_id_size32(input.addb_s);
  uint32_t v1;
  if (4294967295U - v20 < v10)
    v1 = 4294967295U;
  else
    v1 = v10 + v20;
  uint32_t v11 = timestamp_size32(input.addb_t);
  uint32_t v21 = thread_id_size32(input.addb_tid);
  uint32_t v2;
  if (4294967295U - v21 < v11)
    v2 = 4294967295U;
  else
    v2 = v11 + v21;
  if (4294967295U - v2 < v1)
    return 4294967295U;
  else
    return v1 + v2;
}

static uint64_t addb_payload_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t pos10 = record_validator(input, pos);
  uint64_t pos1;
  if (is_error(pos10))
    pos1 = pos10;
  else
    pos1 = slot_id_validator(input, pos10);
  if (is_error(pos1))
    return pos1;
  else
  {
    uint64_t pos11 = timestamp_validator(input, pos1);
    if (is_error(pos11))
      return pos11;
    else
      return thread_id_validator(input, pos11);
  }
}

static uint32_t addb_payload_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return thread_id_jumper(timestamp_jumper(slot_id_jumper(record_jumper(input, pos))));
}

static addb_payload addb_payload_reader(LowParse_Slice_slice input, uint32_t pos)
{
  record x1 = record_reader(input, pos);
  uint32_t pos20 = record_jumper(input, pos);
  uint16_t x2 = slot_id_reader(input, pos20);
  __Zeta_Formats_Aux_Record_record_uint16_t x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = slot_id_jumper(record_jumper(input, pos));
  timestamp x11 = timestamp_reader(input, pos2);
  uint32_t pos21 = timestamp_jumper(pos2);
  uint16_t x20 = thread_id_reader(input, pos21);
  __Zeta_Formats_Aux_Timestamp_timestamp_uint16_t x21 = { .fst = x11, .snd = x20 };
  addb_payload_ res = { .fst = x10, .snd = x21 };
  uint16_t addb_tid = res.snd.snd;
  timestamp addb_t = res.snd.fst;
  uint16_t addb_s = res.fst.snd;
  record addb_r = res.fst.fst;
  return
    ((addb_payload){ .addb_r = addb_r, .addb_s = addb_s, .addb_t = addb_t, .addb_tid = addb_tid });
}

#define AddM 0
#define AddB 1
#define EvictM 2
#define EvictB 3
#define EvictBM 4
#define NextEpoch 5
#define VerifyEpoch 6
#define RunApp 7

typedef uint8_t log_entry_kind;

static log_entry_kind log_entry_kind_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  if (res == 0U)
    return AddM;
  else if (res == 1U)
    return AddB;
  else if (res == 2U)
    return EvictM;
  else if (res == 3U)
    return EvictB;
  else if (res == 4U)
    return EvictBM;
  else if (res == 5U)
    return NextEpoch;
  else if (res == 6U)
    return VerifyEpoch;
  else if (res == 7U)
    return RunApp;
  else
    return AddM;
}

#define Le_payload_AddM 0
#define Le_payload_AddB 1
#define Le_payload_EvictM 2
#define Le_payload_EvictB 3
#define Le_payload_EvictBM 4
#define Le_payload_NextEpoch 5
#define Le_payload_VerifyEpoch 6
#define Le_payload_RunApp 7

typedef uint8_t log_entry_hdr_tags;

typedef struct log_entry_hdr_s
{
  log_entry_hdr_tags tag;
  union {
    addm_payload case_Le_payload_AddM;
    addb_payload case_Le_payload_AddB;
    evictm_payload case_Le_payload_EvictM;
    evictb_payload case_Le_payload_EvictB;
    evictbm_payload case_Le_payload_EvictBM;
    uint8_t case_Le_payload_RunApp;
  }
  ;
}
log_entry_hdr;

static bool uu___is_Le_payload_RunApp(log_entry_hdr projectee)
{
  if (projectee.tag == Le_payload_RunApp)
    return true;
  else
    return false;
}

static uint32_t log_entry_hdr_size32(log_entry_hdr x)
{
  log_entry_kind tg;
  if (x.tag == Le_payload_AddM)
    tg = AddM;
  else if (x.tag == Le_payload_AddB)
    tg = AddB;
  else if (x.tag == Le_payload_EvictM)
    tg = EvictM;
  else if (x.tag == Le_payload_EvictB)
    tg = EvictB;
  else if (x.tag == Le_payload_EvictBM)
    tg = EvictBM;
  else if (x.tag == Le_payload_NextEpoch)
    tg = NextEpoch;
  else if (x.tag == Le_payload_VerifyEpoch)
    tg = VerifyEpoch;
  else if (x.tag == Le_payload_RunApp)
    tg = RunApp;
  else
    tg = KRML_EABORT(log_entry_kind, "unreachable (pattern matches are exhaustive in F*)");
  uint32_t s1 = 1U;
  uint32_t s2;
  if (AddM == tg)
  {
    addm_payload ite;
    if (x.tag == Le_payload_AddM)
      ite = x.case_Le_payload_AddM;
    else
      ite = KRML_EABORT(addm_payload, "unreachable (pattern matches are exhaustive in F*)");
    s2 = addm_payload_size32(ite);
  }
  else if (AddB == tg)
  {
    addb_payload ite;
    if (x.tag == Le_payload_AddB)
      ite = x.case_Le_payload_AddB;
    else
      ite = KRML_EABORT(addb_payload, "unreachable (pattern matches are exhaustive in F*)");
    s2 = addb_payload_size32(ite);
  }
  else if (EvictM == tg)
  {
    evictm_payload ite;
    if (x.tag == Le_payload_EvictM)
      ite = x.case_Le_payload_EvictM;
    else
      ite = KRML_EABORT(evictm_payload, "unreachable (pattern matches are exhaustive in F*)");
    s2 = evictm_payload_size32(ite);
  }
  else if (EvictB == tg)
  {
    evictb_payload ite;
    if (x.tag == Le_payload_EvictB)
      ite = x.case_Le_payload_EvictB;
    else
      ite = KRML_EABORT(evictb_payload, "unreachable (pattern matches are exhaustive in F*)");
    s2 = evictb_payload_size32(ite);
  }
  else if (EvictBM == tg)
  {
    evictbm_payload ite;
    if (x.tag == Le_payload_EvictBM)
      ite = x.case_Le_payload_EvictBM;
    else
      ite = KRML_EABORT(evictbm_payload, "unreachable (pattern matches are exhaustive in F*)");
    s2 = evictbm_payload_size32(ite);
  }
  else if (NextEpoch == tg)
    s2 = 0U;
  else if (VerifyEpoch == tg)
    s2 = 0U;
  else
  {
    uint8_t ite;
    if (x.tag == Le_payload_RunApp)
      ite = x.case_Le_payload_RunApp;
    else
      ite = KRML_EABORT(uint8_t, "unreachable (pattern matches are exhaustive in F*)");
    s2 = runapp_payload_hdr_size32(ite);
  }
  return s1 + s2;
}

static uint64_t log_entry_hdr_validator(LowParse_Slice_slice input, uint64_t pos)
{
  uint64_t len_after_tag;
  if ((uint64_t)input.len - pos < 1ULL)
    len_after_tag = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    len_after_tag = pos + 1ULL;
  if (is_error(len_after_tag))
    return len_after_tag;
  else
  {
    uint8_t k_ = input.base[(uint32_t)pos];
    if (k_ == 0U)
      return addm_payload_validator(input, len_after_tag);
    else if (k_ == 1U)
      return addb_payload_validator(input, len_after_tag);
    else if (k_ == 2U)
      return evictm_payload_validator(input, len_after_tag);
    else if (k_ == 3U)
      return evictb_payload_validator(input, len_after_tag);
    else if (k_ == 4U)
      return evictbm_payload_validator(input, len_after_tag);
    else if (k_ == 5U)
      if ((uint64_t)input.len - len_after_tag < 0ULL)
        return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        return len_after_tag + 0ULL;
    else if (k_ == 6U)
      if ((uint64_t)input.len - len_after_tag < 0ULL)
        return VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        return len_after_tag + 0ULL;
    else if (k_ == 7U)
      return runapp_payload_hdr_validator(input, len_after_tag);
    else
      return VALIDATOR_ERROR_GENERIC;
  }
}

static uint32_t log_entry_hdr_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + 1U;
  uint8_t k_ = input.base[pos];
  if (k_ == 0U)
    return addm_payload_jumper(input, pos_after_tag);
  else if (k_ == 1U)
    return addb_payload_jumper(input, pos_after_tag);
  else if (k_ == 2U)
    return evictm_payload_jumper(pos_after_tag);
  else if (k_ == 3U)
    return evictb_payload_jumper(pos_after_tag);
  else if (k_ == 4U)
    return evictbm_payload_jumper(pos_after_tag);
  else if (k_ == 5U)
    return pos_after_tag + 0U;
  else if (k_ == 6U)
    return pos_after_tag + 0U;
  else if (k_ == 7U)
    return runapp_payload_hdr_jumper(pos_after_tag);
  else
    return 0U;
}

static log_entry_hdr log_entry_hdr_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t res = input.base[pos];
  log_entry_kind k;
  if (res == 0U)
    k = AddM;
  else if (res == 1U)
    k = AddB;
  else if (res == 2U)
    k = EvictM;
  else if (res == 3U)
    k = EvictB;
  else if (res == 4U)
    k = EvictBM;
  else if (res == 5U)
    k = NextEpoch;
  else if (res == 6U)
    k = VerifyEpoch;
  else if (res == 7U)
    k = RunApp;
  else
    k = AddM;
  uint32_t pos_ = pos + 1U;
  if (AddM == k)
  {
    addm_payload res = addm_payload_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_AddM, { .case_Le_payload_AddM = res } });
  }
  else if (AddB == k)
  {
    addb_payload res = addb_payload_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_AddB, { .case_Le_payload_AddB = res } });
  }
  else if (EvictM == k)
  {
    evictm_payload res = evictm_payload_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_EvictM, { .case_Le_payload_EvictM = res } });
  }
  else if (EvictB == k)
  {
    evictb_payload res = evictb_payload_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_EvictB, { .case_Le_payload_EvictB = res } });
  }
  else if (EvictBM == k)
  {
    evictbm_payload res = evictbm_payload_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_EvictBM, { .case_Le_payload_EvictBM = res } });
  }
  else if (NextEpoch == k)
    return ((log_entry_hdr){ .tag = Le_payload_NextEpoch });
  else if (VerifyEpoch == k)
    return ((log_entry_hdr){ .tag = Le_payload_VerifyEpoch });
  else
  {
    uint8_t res = runapp_payload_hdr_reader(input, pos_);
    return ((log_entry_hdr){ .tag = Le_payload_RunApp, { .case_Le_payload_RunApp = res } });
  }
}

static uint32_t log_entry_hdr_accessor_tag(uint32_t pos)
{
  return pos;
}

static Zeta_Steel_LogEntry_Types_log_entry synth_log_entry_false(log_entry_hdr x)
{
  if (x.tag == Le_payload_AddM)
  {
    addm_payload apl = x.case_Le_payload_AddM;
    Zeta_Steel_LogEntry_Types_record r = synth_record(apl.addm_r);
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_AddM,
          { .case_AddM = { .s = apl.addm_s, .s_ = apl.addm_s2, .r = r } }
        }
      );
  }
  else if (x.tag == Le_payload_AddB)
  {
    addb_payload apl = x.case_Le_payload_AddB;
    Zeta_Steel_LogEntry_Types_record r = synth_record(apl.addb_r);
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_AddB,
          {
            .case_AddB = {
              .s = apl.addb_s,
              .ts = synth_timestamp(apl.addb_t),
              .tid = apl.addb_tid,
              .r = r
            }
          }
        }
      );
  }
  else if (x.tag == Le_payload_NextEpoch)
    return ((Zeta_Steel_LogEntry_Types_log_entry){ .tag = Zeta_Steel_LogEntry_Types_NextEpoch });
  else if (x.tag == Le_payload_VerifyEpoch)
    return ((Zeta_Steel_LogEntry_Types_log_entry){ .tag = Zeta_Steel_LogEntry_Types_VerifyEpoch });
  else if (x.tag == Le_payload_EvictM)
  {
    evictm_payload epl = x.case_Le_payload_EvictM;
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_EvictM,
          { .case_EvictM = { .s = epl.evictm_s, .s_ = epl.evictm_s2 } }
        }
      );
  }
  else if (x.tag == Le_payload_EvictB)
  {
    evictb_payload epl = x.case_Le_payload_EvictB;
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_EvictB,
          { .case_EvictB = { .s1 = epl.evictb_s, .t = synth_timestamp(epl.evictb_t) } }
        }
      );
  }
  else if (x.tag == Le_payload_EvictBM)
  {
    evictbm_payload epl = x.case_Le_payload_EvictBM;
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_EvictBM,
          {
            .case_EvictBM = {
              .s2 = epl.evictbm_s,
              .s_1 = epl.evictbm_s2,
              .t1 = synth_timestamp(epl.evictbm_t)
            }
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

static Zeta_Steel_LogEntry_Types_log_entry
synth_log_entry_true(log_entry_hdr x, uint32_t pl_len)
{
  if (x.tag == Le_payload_RunApp)
  {
    uint8_t rpl = x.case_Le_payload_RunApp;
    return
      (
        (Zeta_Steel_LogEntry_Types_log_entry){
          .tag = Zeta_Steel_LogEntry_Types_RunApp,
          { .case_RunApp = { .fid = rpl, .rest = pl_len } }
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

static log_entry_hdr synth_log_entry_recip_hdr(Zeta_Steel_LogEntry_Types_log_entry y)
{
  if (y.tag == Zeta_Steel_LogEntry_Types_AddM)
  {
    Zeta_Steel_LogEntry_Types_record r = y.case_AddM.r;
    uint16_t s2 = y.case_AddM.s_;
    uint16_t s = y.case_AddM.s;
    record r0 = synth_record_recip(r);
    return
      (
        (log_entry_hdr){
          .tag = Le_payload_AddM,
          { .case_Le_payload_AddM = { .addm_r = r0, .addm_s = s, .addm_s2 = s2 } }
        }
      );
  }
  else if (y.tag == Zeta_Steel_LogEntry_Types_AddB)
  {
    Zeta_Steel_LogEntry_Types_record r = y.case_AddB.r;
    uint16_t tid = y.case_AddB.tid;
    Zeta_Steel_LogEntry_Types_timestamp t = y.case_AddB.ts;
    uint16_t s = y.case_AddB.s;
    record r0 = synth_record_recip(r);
    return
      (
        (log_entry_hdr){
          .tag = Le_payload_AddB,
          {
            .case_Le_payload_AddB = {
              .addb_r = r0,
              .addb_s = s,
              .addb_t = synth_timestamp_recip(t),
              .addb_tid = tid
            }
          }
        }
      );
  }
  else if (y.tag == Zeta_Steel_LogEntry_Types_RunApp)
  {
    uint8_t rpl = y.case_RunApp.fid;
    return ((log_entry_hdr){ .tag = Le_payload_RunApp, { .case_Le_payload_RunApp = rpl } });
  }
  else if (y.tag == Zeta_Steel_LogEntry_Types_NextEpoch)
    return ((log_entry_hdr){ .tag = Le_payload_NextEpoch });
  else if (y.tag == Zeta_Steel_LogEntry_Types_VerifyEpoch)
    return ((log_entry_hdr){ .tag = Le_payload_VerifyEpoch });
  else if (y.tag == Zeta_Steel_LogEntry_Types_EvictM)
  {
    uint16_t s2 = y.case_EvictM.s_;
    uint16_t s = y.case_EvictM.s;
    return
      (
        (log_entry_hdr){
          .tag = Le_payload_EvictM,
          { .case_Le_payload_EvictM = { .evictm_s = s, .evictm_s2 = s2 } }
        }
      );
  }
  else if (y.tag == Zeta_Steel_LogEntry_Types_EvictB)
  {
    Zeta_Steel_LogEntry_Types_timestamp t = y.case_EvictB.t;
    uint16_t s = y.case_EvictB.s1;
    return
      (
        (log_entry_hdr){
          .tag = Le_payload_EvictB,
          { .case_Le_payload_EvictB = { .evictb_s = s, .evictb_t = synth_timestamp_recip(t) } }
        }
      );
  }
  else if (y.tag == Zeta_Steel_LogEntry_Types_EvictBM)
  {
    Zeta_Steel_LogEntry_Types_timestamp t = y.case_EvictBM.t1;
    uint16_t s2 = y.case_EvictBM.s_1;
    uint16_t s = y.case_EvictBM.s2;
    return
      (
        (log_entry_hdr){
          .tag = Le_payload_EvictBM,
          {
            .case_Le_payload_EvictBM = {
              .evictbm_s = s,
              .evictbm_s2 = s2,
              .evictbm_t = synth_timestamp_recip(t)
            }
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

static uint32_t runapp_payload_offset_(Zeta_Steel_LogEntry_Types_log_entry e)
{
  if (e.tag == Zeta_Steel_LogEntry_Types_RunApp)
  {
    log_entry_hdr h = synth_log_entry_recip_hdr(e);
    return log_entry_hdr_size32(h) + 4U;
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

uint32_t zeta__runapp_payload_offset(Zeta_Steel_LogEntry_Types_log_entry e)
{
  return runapp_payload_offset_(e);
}

static stamped_record synth_stamped_record_recip(Zeta_Steel_LogEntry_Types_stamped_record x)
{
  return
    (
      (stamped_record){
        .sr_record = synth_record_recip(x.record),
        .sr_timestamp = synth_timestamp_recip(x.timestamp),
        .sr_thread_id = x.thread_id
      }
    );
}

FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t
zeta__parser_log_entry(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  KRML_MAYBE_UNUSED_VAR(len);
  uint8_t *sl_base = a + offset;
  LowParse_Slice_slice sl = { .base = sl_base, .len = slice_len };
  uint64_t pos_after_t = log_entry_hdr_validator(sl, 0ULL);
  uint64_t consumed;
  if (is_error(pos_after_t))
    consumed = pos_after_t;
  else
  {
    uint32_t pos_tag = log_entry_hdr_accessor_tag((uint32_t)0ULL);
    log_entry_kind tag = log_entry_kind_reader(sl, pos_tag);
    bool b = tag == RunApp;
    if (b)
    {
      uint64_t res;
      if ((uint64_t)sl.len - pos_after_t < 4ULL)
        res = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      else
        res = pos_after_t + 4ULL;
      if (is_error(res))
        consumed = res;
      else
      {
        uint32_t va = load32_be(sl.base + (uint32_t)pos_after_t);
        if (va <= 2147483647U)
          if ((uint64_t)sl.len - res < (uint64_t)va)
            consumed = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          else
          {
            uint64_t pos_ = (uint64_t)((uint32_t)res + va);
            if (is_error(pos_))
              if (pos_ == VALIDATOR_ERROR_NOT_ENOUGH_DATA)
                consumed = VALIDATOR_ERROR_GENERIC;
              else
                consumed = pos_;
            else
              consumed = pos_;
          }
        else
          consumed = VALIDATOR_ERROR_GENERIC;
      }
    }
    else if ((uint64_t)sl.len - pos_after_t < 0ULL)
      consumed = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    else
      consumed = pos_after_t + 0ULL;
  }
  if (is_error(consumed))
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    uint32_t consumed1 = (uint32_t)consumed;
    log_entry_hdr hdr = log_entry_hdr_reader(sl, 0U);
    if (uu___is_Le_payload_RunApp(hdr))
    {
      uint32_t pos_pl = log_entry_hdr_jumper(sl, 0U);
      uint32_t len1 = load32_be(sl.base + pos_pl);
      uint32_t len_pl = len1;
      Zeta_Steel_LogEntry_Types_log_entry res = synth_log_entry_true(hdr, len_pl);
      return
        (
          (FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = res, .snd = consumed1 }
          }
        );
    }
    else
    {
      Zeta_Steel_LogEntry_Types_log_entry res = synth_log_entry_false(hdr);
      return
        (
          (FStar_Pervasives_Native_option__Zeta_Steel_LogEntry_Types_log_entry___uint32_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = res, .snd = consumed1 }
          }
        );
    }
  }
}

uint32_t
zeta__serialize_stamped_record(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_stamped_record v
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  return stamped_record_lserializer(synth_stamped_record_recip(v), (uint8_t *)a, offset);
}

uint32_t
zeta__serialize_value(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_value v
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  return value_lserializer(synth_value_recip(v), (uint8_t *)a, offset);
}

FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t
zeta__parser_u256(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  KRML_MAYBE_UNUSED_VAR(len);
  uint8_t *sl_base = a + offset;
  LowParse_Slice_slice sl = { .base = sl_base, .len = slice_len };
  uint64_t consumed = u256_validator(sl, 0ULL);
  if (is_error(consumed))
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    uint32_t consumed1 = (uint32_t)consumed;
    u256 res = u256_reader(sl, 0U);
    Zeta_Steel_KeyUtils_u256 res0 = synth_u256(res);
    return
      (
        (FStar_Pervasives_Native_option__Zeta_Steel_KeyUtils_u256___uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = consumed1 }
        }
      );
  }
}

uint32_t
zeta__serialize_timestamp(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_timestamp v
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  return timestamp_lserializer(synth_timestamp_recip(v), (uint8_t *)a, offset);
}

