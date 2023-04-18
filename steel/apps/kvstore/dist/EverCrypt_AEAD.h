

#ifndef __EverCrypt_AEAD_H
#define __EverCrypt_AEAD_H

#include "krmllib.h"

typedef uint8_t EverCrypt_AEAD_error_code;

extern uint8_t EverCrypt_AEAD_create_in(uint8_t a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

extern uint8_t
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *plain_unused,
  uint32_t plain_len,
  uint8_t *cipher_unused,
  uint8_t *tag
);

extern uint8_t
EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *plain_unused,
  uint32_t plain_len,
  uint8_t *cipher_unused,
  uint8_t *tag
);


#define __EverCrypt_AEAD_H_DEFINED
#endif
