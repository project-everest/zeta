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

uint16_t UInt256::GetLargestCommonSuffixSize(const UInt256& v1, const UInt256& v2)
{
    for (int i = 3 ; i >= 0 ; --i)
    {
        if (v1.bytes_[i] != v2.bytes_[i])
        {

            return ((3-i) << 6) + __builtin_ctzll(bswap_64(v1.bytes_[i]) ^
                                                  bswap_64(v2.bytes_[i]));
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

void UInt256::ZeroPrefix(uint64_t size)
{
    assert(size <= 256);

    auto n = (size >> 6);
    assert(n <= 4);

    for (auto i = 0 ; i < n ; ++i) {
        bytes_[i] = 0;
    }

    if (n < 4) {
        auto s = (size & 0x3f);
        assert(s < 64);
        bytes_[n] &= bswap_64(~0ull >> s);
    }
}

bool UInt256::IsPrefixZero(uint64_t size) const
{
    assert(size <= 256);

    auto n = (size >> 6);
    assert(n <= 4);

    for (auto i = 0 ; i < n ; ++i) {
        if (bytes_[i] != 0) {
            return false;
        }
    }

    if (n < 4) {
        auto s = (size & 0x3f);
        assert(s < 64);
        if ((bytes_[n] & bswap_64(~(~0ull >> s))) != 0) {
            return false;
        }
    }

    return true;
}

BaseKey BaseKey::GetNormalizedKey() const
{
    auto path = GetPath();
    path.ZeroPrefix(BaseKey::LeafDepth - GetDepth());

    return BaseKey { path, GetDepth() };
}
