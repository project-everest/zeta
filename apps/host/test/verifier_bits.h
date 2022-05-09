/**
 * A copy of Zeta_verifier low level representations and operations for testing
 * the host code that implements the same.
 */

#pragma once

#include <byteswap.h>
#include <stdint.h>
#include <string.h>

#define be64toh(x) bswap_64 (x)

#define load16_le(b) (le16toh(load16(b)))
#define store16_le(b, i) (store16(b, htole16(i)))
#define load16_be(b) (be16toh(load16(b)))
#define store16_be(b, i) (store16(b, htobe16(i)))

#define load32_le(b) (le32toh(load32(b)))
#define store32_le(b, i) (store32(b, htole32(i)))
#define load32_be(b) (be32toh(load32(b)))
#define store32_be(b, i) (store32(b, htobe32(i)))

#define load64_le(b) (le64toh(load64(b)))
#define store64_le(b, i) (store64(b, htole64(i)))
#define load64_be(b) (be64toh(load64(b)))
#define store64_be(b, i) (store64(b, htobe64(i)))

struct Verifier_u256
{
  uint64_t v3;
  uint64_t v2;
  uint64_t v1;
  uint64_t v0;
};

struct Verifier_base_key
{
  Verifier_u256 k;
  uint16_t significant_digits;
};

struct LowParse_Slice_slice
{
  uint8_t *base;
  uint32_t len;
};

bool ith_bit(Verifier_u256 kk, uint16_t i);

Verifier_u256 u256_reader(LowParse_Slice_slice input, uint32_t pos);

bool
is_proper_descendent(
  Verifier_base_key k0,
  Verifier_base_key k1);

Verifier_base_key truncate_key(Verifier_base_key k, uint16_t w);
