#include <verifier-bits.h>

struct __uint32_t_uint32_t
{
  uint32_t fst;
  uint32_t snd;
};

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

static bool ith_bit_64(uint64_t x, uint32_t i)
{
  return (x >> i) % (uint64_t)2U == (uint64_t)1U;
}

bool ith_bit(Verifier_u256 kk, uint16_t i)
{
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

struct __uint64_t_uint64_t
{
  uint64_t fst;
  uint64_t snd;
};

typedef struct u256__s
{
  __uint64_t_uint64_t fst;
  __uint64_t_uint64_t snd;
}
u256_;

inline static uint64_t load64(uint8_t *b) {
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}

Verifier_u256 u256_reader(LowParse_Slice_slice input, uint32_t pos)
{
  uint8_t *x00 = input.base;
  uint64_t x1 = load64_be(x00 + pos);
  uint32_t pos20 = pos + (uint32_t)8U;
  uint8_t *x01 = input.base;
  uint64_t x2 = load64_be(x01 + pos20);
  __uint64_t_uint64_t x10 = { .fst = x1, .snd = x2 };
  uint32_t pos2 = pos + (uint32_t)8U + (uint32_t)8U;
  uint8_t *x02 = input.base;
  uint64_t x11 = load64_be(x02 + pos2);
  uint32_t pos21 = pos2 + (uint32_t)8U;
  uint8_t *x0 = input.base;
  uint64_t x20 = load64_be(x0 + pos21);
  __uint64_t_uint64_t x21 = { .fst = x11, .snd = x20 };
  u256_ res = { .fst = x10, .snd = x21 };
  uint64_t v0 = res.snd.snd;
  uint64_t v1 = res.snd.fst;
  uint64_t v2 = res.fst.snd;
  uint64_t v3 = res.fst.fst;
  return ((Verifier_u256){ .v3 = v3, .v2 = v2, .v1 = v1, .v0 = v0 });
}
