

#ifndef __Zeta_KeyValueStore_Formats_LowStar_H
#define __Zeta_KeyValueStore_Formats_LowStar_H

#include "krmllib.h"




typedef struct Zeta_KeyValueStore_Formats_Types_vget_args_t_s
{
  uint64_t vget_key;
  uint64_t vget_value;
  uint16_t vget_slot;
}
Zeta_KeyValueStore_Formats_Types_vget_args_t;

typedef struct Zeta_KeyValueStore_Formats_Types_vput_args_t_s
{
  uint64_t vput_key;
  uint64_t vput_value;
  uint16_t vput_slot;
}
Zeta_KeyValueStore_Formats_Types_vput_args_t;

typedef struct K___uint64_t_uint32_t_s
{
  uint64_t fst;
  uint32_t snd;
}
K___uint64_t_uint32_t;

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__uint64_t___uint32_t_tags;

typedef struct FStar_Pervasives_Native_option__uint64_t___uint32_t_s
{
  FStar_Pervasives_Native_option__uint64_t___uint32_t_tags tag;
  K___uint64_t_uint32_t v;
}
FStar_Pervasives_Native_option__uint64_t___uint32_t;

FStar_Pervasives_Native_option__uint64_t___uint32_t
kvstore_key_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

uint32_t kvstore_key_serializer(uint32_t len, uint32_t offset, uint8_t *a, uint64_t v);

FStar_Pervasives_Native_option__uint64_t___uint32_t
kvstore_value_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

uint32_t kvstore_value_serializer(uint32_t len, uint32_t offset, uint8_t *a, uint64_t v);

typedef struct K___Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t_s
{
  Zeta_KeyValueStore_Formats_Types_vget_args_t fst;
  uint32_t snd;
}
K___Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t;

typedef struct
FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t_s
{
  FStar_Pervasives_Native_option__uint64_t___uint32_t_tags tag;
  K___Zeta_KeyValueStore_Formats_Types_vget_args_t_uint32_t v;
}
FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t;

FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vget_args_t___uint32_t
kvstore_vget_args_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

typedef struct K___Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t_s
{
  Zeta_KeyValueStore_Formats_Types_vput_args_t fst;
  uint32_t snd;
}
K___Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t;

typedef struct
FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t_s
{
  FStar_Pervasives_Native_option__uint64_t___uint32_t_tags tag;
  K___Zeta_KeyValueStore_Formats_Types_vput_args_t_uint32_t v;
}
FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t;

FStar_Pervasives_Native_option__Zeta_KeyValueStore_Formats_Types_vput_args_t___uint32_t
kvstore_vput_args_parser(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);


#define __Zeta_KeyValueStore_Formats_LowStar_H_DEFINED
#endif
