#include <ZetaFormats.h>

uint64_t App_val_app_val_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < (uint64_t)8U)
      return 0xffffffffffffffffull;
  else
      return pos + (uint64_t)8U;
}

uint32_t App_val_app_val_jumper(LowParse_Slice_slice input, uint32_t pos)
{
    return pos + (uint32_t)8U;
}

uint64_t App_val_app_val_reader(LowParse_Slice_slice sl, uint32_t pos)
{
    uint8_t *x0 = sl.base;
    return load64_be(x0 + pos);
}

uint32_t App_val_app_val_lserializer(uint64_t v, uint8_t *b, uint32_t pos)
{
    store64_be(b + pos, v);
    return (uint32_t)8U;
}

uint64_t App_key_app_key_validator(LowParse_Slice_slice sl, uint64_t pos)
{
  if ((uint64_t)sl.len - pos < (uint64_t)8U)
      return 0xffffffffffffffffull;
  else
      return pos + (uint64_t)8U;
}

uint32_t App_key_app_key_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)8U;
}

uint64_t App_key_app_key_reader(LowParse_Slice_slice sl, uint32_t pos)
{
  uint8_t *x0 = sl.base;
  return load64_be(x0 + pos);
}

uint32_t App_key_app_key_lserializer(uint64_t v, uint8_t *b, uint32_t pos)
{
  store64_be(b + pos, v);
  return (uint32_t)8U;
}


uint32_t
Zeta_Formats_Aux_Application_value_Size_application_value_size32(
  Zeta_Steel_ApplicationTypes_value_type x
)
{
    /* TODO: buggy code remove */
    return sizeof(x);
}

uint64_t
Zeta_Formats_Aux_Application_value_Low_application_value_validator(
  LowParse_Slice_slice x0,
  uint64_t x1
)
{
    return App_val_app_val_validator(x0, x1);
}

uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_jumper(
  LowParse_Slice_slice x0,
  uint32_t x1
)
{
    return App_val_app_val_jumper(x0, x1);
}

Zeta_Steel_ApplicationTypes_value_type
Zeta_Formats_Aux_Application_value_Low_application_value_reader(
  LowParse_Slice_slice x0,
  uint32_t x1
)
{
    return App_val_app_val_reader(x0, x1);
}

uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_lserializer(
  Zeta_Steel_ApplicationTypes_value_type v,
  uint8_t *b,
  uint32_t pos
)
{
    return App_val_app_val_lserializer(v, b, pos);
}

uint32_t
Zeta_Formats_Aux_Application_key_Size_application_key_size32(
  Zeta_Steel_ApplicationTypes_key_type k
)
{
    /* TODO: remove buggy code */
    return sizeof(k);
}

uint64_t
Zeta_Formats_Aux_Application_key_Low_application_key_validator(
  LowParse_Slice_slice sl,
  uint64_t pos
)
{
    return App_key_app_key_validator(sl, pos);
}

uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_jumper(
  LowParse_Slice_slice input,
  uint32_t pos
)
{
    return App_key_app_key_jumper(input, pos);
}

Zeta_Steel_ApplicationTypes_key_type
Zeta_Formats_Aux_Application_key_Low_application_key_reader(
  LowParse_Slice_slice sl,
  uint32_t pos
)
{
    return App_key_app_key_reader(sl, pos);
}

uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_lserializer(
  Zeta_Steel_ApplicationTypes_key_type v,
  uint8_t *b,
  uint32_t pos
)
{
    return App_key_app_key_lserializer(v, b, pos);
}
