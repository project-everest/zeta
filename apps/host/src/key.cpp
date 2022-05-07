#include <byteswap.h>
#include <key.h>

using namespace Zeta;

BaseKey BaseKey::Root { };

UInt256 UInt256::Deserialize(const uint8_t* buf, size_t len)
{
    UInt256 ui256;

    size_t n = (len >= 32)? 32 : len;
    memcpy(ui256.Bytes(), buf, len);
    return ui256;
}

uint16_t UInt256::GetLargestCommonPrefixSize(const UInt256& v1, const UInt256& v2)
{
    for (uint8_t i = 0 ; i < 4 ; ++i)
    {
        if (v1.bytes_[i] != v2.bytes_[i])
        {
            return (i << 6) + __builtin_clzll(v1.bytes_[i] ^ v2.bytes_[i]);
        }
    }

    return 256;
}

uint8_t UInt256::GetBit(uint8_t p) const
{
    uint8_t n = 3 - (p >> 6);
    assert (n < 4);

    uint64_t w = bytes_[n];
    w = bswap_64(w);

    return (w >> (p & 0x3f)) & 0x01;
}

void UInt256::SetBit(uint8_t p)
{
    uint8_t n = 3 - (p >> 6);
    assert (n < 4);

    uint8_t s = (p & 0x3f);
    bytes_[n] |= bswap_64(1ull << s);
}

void UInt256::ClearBit(uint8_t p)
{
    uint8_t n = 3 - (p >> 6);
    assert (n < 4);

    uint8_t s = (p & 0x3f);
    bytes_[n] &= bswap_64(~1ull << s);
}
