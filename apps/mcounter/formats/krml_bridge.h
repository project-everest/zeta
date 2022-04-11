#pragma once

#include <ZetaFormatsApplicationTypes.h>

/* mirror LowParse slice */
typedef struct _kb_slice
{
    uint8_t *base;
    uint32_t len;
} kb_slice;

typedef struct _kb_new_p
{
    app_key_t k;
    slot_t s;
} kb_new_p;

typedef struct _kb_incr_p
{
    app_key_t k;
    slot_t s;
} kb_incr_p;

typedef struct _kb_get_p
{
    app_key_t k;
    slot_t s;
} kb_get_p;

uint64_t kb_app_key_validator(uint8_t *base, uint32_t len, uint64_t pos);

uint32_t kb_app_key_jumper(uint8_t *base, uint32_t len, uint32_t pos);

uint64_t kb_app_key_reader(uint8_t *base, uint32_t len, uint32_t pos);

uint32_t kb_app_key_lserializer(app_key_t v, uint8_t *b, uint32_t pos);

uint64_t kb_new_p_validator(uint8_t *base, uint32_t len, uint64_t pos);

uint32_t kb_new_p_jumper(uint8_t *base, uint32_t len, uint32_t pos);

kb_new_p kb_new_p_reader(uint8_t *base, uint32_t len, uint32_t pos);

uint32_t kb_new_p_lserializer(kb_new_p x, uint8_t *input, uint32_t pos);
