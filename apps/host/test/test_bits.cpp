#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <key.h>
#include <verifier_bits.h>

using namespace Zeta;

static bool equal (const Verifier_u256& v256, const UInt256& h256)
{
    for (uint32_t p = 0 ; p < 256 ; ++p) {
        uint8_t hb = h256.GetBit(static_cast<uint8_t>(p));
        uint8_t vb = ith_bit(v256, static_cast<uint16_t>(p))? 1 : 0;

        if (hb != vb) {
            return false;
        }
    }

    return true;
}

// Do the host and verifier representations implement get-bit the same way
//
TEST_CASE("test get-bit position")
{
    uint8_t buf[32];

    for (int i = 0 ; i < 32 ; ++i) {
        buf[i] = i;
    }

    auto v256 = u256_reader ( { buf, 32}, 0);
    UInt256 h256;

    memcpy (h256.Bytes(), buf, 32);
    REQUIRE(equal(v256, h256));
}

TEST_CASE("test u256 set-bit")
{
    UInt256 h256 {};

    for (uint32_t p = 0 ; p < 256 ; ++p) {
        auto p8 = static_cast<uint8_t>(p);
        REQUIRE(h256.GetBit(p8) == 0);

        h256.SetBit(p8);
        REQUIRE(h256.GetBit(p8) == 1);
    }
}

TEST_CASE("Test clearbit")
{

    uint64_t v = 0xaaaaaaaaaaaaaaaaull;
    UInt256 a {v, v, v, v};

    for (int i = 0 ; i < 256 ; ++i)
    {
        if (a.GetBit(static_cast<uint8_t>(i)) == 1)
        {
            a.ClearBit(static_cast<uint8_t>(i));
        }
    }


    UInt256 exp {0, 0, 0, 0};
    REQUIRE(a == exp);
}
