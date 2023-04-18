

#include "Zeta_KeyValueStore_Formats_LowStar.h"

#define VALIDATOR_MAX_LENGTH ((uint64_t)4294967295U)

static inline bool is_error(uint64_t positionOrError)
{
  return positionOrError > VALIDATOR_MAX_LENGTH;
}

#define VALIDATOR_ERROR_NOT_ENOUGH_DATA ((uint64_t)8589934592U)

typedef struct __uint64_t_uint64_t_s
{
  uint64_t fst;
  uint64_t snd;
}
__uint64_t_uint64_t;

typedef struct __uint64_t___uint64_t_uint16_t_s
{
  __uint64_t_uint64_t fst;
  uint16_t snd;
}
__uint64_t___uint64_t_uint16_t;

static Zeta_KeyValueStore_Formats_Types_vget_args_t
synth_vget_args(__uint64_t___uint64_t_uint16_t uu___)
{
  uint16_t vget_slot = uu___.snd;
  uint64_t vget_value = uu___.fst.snd;
  uint64_t vget_key = uu___.fst.fst;
  return
    (
      (Zeta_KeyValueStore_Formats_Types_vget_args_t){
        .vget_key = vget_key,
        .vget_value = vget_value,
        .vget_slot = vget_slot
      }
    );
}

static Zeta_KeyValueStore_Formats_Types_vput_args_t
synth_vput_args(__uint64_t___uint64_t_uint16_t uu___)
{
  uint16_t vput_slot = uu___.snd;
  uint64_t vput_value = uu___.fst.snd;
  uint64_t vput_key = uu___.fst.fst;
  return
    (
      (Zeta_KeyValueStore_Formats_Types_vput_args_t){
        .vput_key = vput_key,
        .vput_value = vput_value,
        .vput_slot = vput_slot
      }
    );
}

FStar_Pervasives_Native_option__uint64_t___uint32_t
kvstore_key_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  uint8_t *a_ = a + offset;
  uint64_t is_err;
  if ((uint64_t)slice_len - (uint64_t)0U < (uint64_t)8U)
    is_err = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    is_err = (uint64_t)8U;
  if (is_error(is_err))
    return
      ((FStar_Pervasives_Native_option__uint64_t___uint32_t){ .tag = FStar_Pervasives_Native_None });
  else
  {
    uint64_t res = load64_be(a_);
    return
      (
        (FStar_Pervasives_Native_option__uint64_t___uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res, .snd = (uint32_t)is_err }
        }
      );
  }
}

uint32_t kvstore_key_serializer(uint32_t len, uint32_t offset, uint8_t *a, uint64_t v)
{
  uint8_t *a_ = a + offset;
  store64_be(a_, v);
  return (uint32_t)8U;
}

FStar_Pervasives_Native_option__uint64_t___uint32_t
kvstore_value_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  uint8_t *a_ = a + offset;
  uint64_t is_err;
  if ((uint64_t)slice_len - (uint64_t)0U < (uint64_t)8U)
    is_err = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    is_err = (uint64_t)8U;
  if (is_error(is_err))
    return
      ((FStar_Pervasives_Native_option__uint64_t___uint32_t){ .tag = FStar_Pervasives_Native_None });
  else
  {
    uint64_t res = load64_be(a_);
    return
      (
        (FStar_Pervasives_Native_option__uint64_t___uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res, .snd = (uint32_t)is_err }
        }
      );
  }
}

uint32_t kvstore_value_serializer(uint32_t len, uint32_t offset, uint8_t *a, uint64_t v)
{
  uint8_t *a_ = a + offset;
  store64_be(a_, v);
  return (uint32_t)8U;
}

FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t
kvstore_vget_args_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  uint8_t *a_ = a + offset;
  uint64_t pos10;
  if ((uint64_t)slice_len - (uint64_t)0U < (uint64_t)8U)
    pos10 = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    pos10 = (uint64_t)8U;
  uint64_t pos1;
  if (is_error(pos10))
    pos1 = pos10;
  else if ((uint64_t)slice_len - pos10 < (uint64_t)8U)
    pos1 = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    pos1 = pos10 + (uint64_t)8U;
  uint64_t is_err;
  if (is_error(pos1))
    is_err = pos1;
  else if ((uint64_t)slice_len - pos1 < (uint64_t)2U)
    is_err = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    is_err = pos1 + (uint64_t)2U;
  if (is_error(is_err))
    return
      (
        (FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    uint64_t x1 = load64_be(a_);
    uint32_t pos20 = (uint32_t)8U;
    uint64_t x2 = load64_be(a_ + pos20);
    __uint64_t_uint64_t x10 = { .fst = x1, .snd = x2 };
    uint32_t pos2 = (uint32_t)8U + (uint32_t)8U;
    uint16_t x20 = load16_be(a_ + pos2);
    __uint64_t___uint64_t_uint16_t res = { .fst = x10, .snd = x20 };
    Zeta_KeyValueStore_Formats_Types_vget_args_t res0 = synth_vget_args(res);
    return
      (
        (FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = (uint32_t)is_err }
        }
      );
  }
}

FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t
kvstore_vput_args_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a)
{
  uint8_t *a_ = a + offset;
  uint64_t pos10;
  if ((uint64_t)slice_len - (uint64_t)0U < (uint64_t)8U)
    pos10 = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    pos10 = (uint64_t)8U;
  uint64_t pos1;
  if (is_error(pos10))
    pos1 = pos10;
  else if ((uint64_t)slice_len - pos10 < (uint64_t)8U)
    pos1 = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    pos1 = pos10 + (uint64_t)8U;
  uint64_t is_err;
  if (is_error(pos1))
    is_err = pos1;
  else if ((uint64_t)slice_len - pos1 < (uint64_t)2U)
    is_err = VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    is_err = pos1 + (uint64_t)2U;
  if (is_error(is_err))
    return
      (
        (FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else
  {
    uint64_t x1 = load64_be(a_);
    uint32_t pos20 = (uint32_t)8U;
    uint64_t x2 = load64_be(a_ + pos20);
    __uint64_t_uint64_t x10 = { .fst = x1, .snd = x2 };
    uint32_t pos2 = (uint32_t)8U + (uint32_t)8U;
    uint16_t x20 = load16_be(a_ + pos2);
    __uint64_t___uint64_t_uint16_t res = { .fst = x10, .snd = x20 };
    Zeta_KeyValueStore_Formats_Types_vput_args_t res0 = synth_vput_args(res);
    return
      (
        (FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = res0, .snd = (uint32_t)is_err }
        }
      );
  }
}

