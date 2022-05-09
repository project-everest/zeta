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

static bool equal (const Verifier_base_key& vbk, const BaseKey& hbk)
{
    if (vbk.significant_digits != hbk.GetDepth()) return false;

    for (uint32_t p = 0 ; p < hbk.GetDepth() ; ++p) {
        uint8_t hb = hbk.GetPath().GetBit(static_cast<uint8_t>(p));
        uint8_t vb = ith_bit(vbk.k, static_cast<uint16_t>(p))? 1 : 0;

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
    auto h256 = UInt256::Deserialize(buf, 32);

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

TEST_CASE("test zero prefix")
{
    uint64_t v = 0xffffffffffffffffull;


    uint64_t ps[] = { 32, 96, 160, 224 };

    for (int i = 0 ; i < 4 ; ++i) {
        UInt256 path {v, v, v, v};
        path.ZeroPrefix(ps[i]);

        auto p = 256 - ps[i];

        for (int j = 0 ; j < p ; ++j) {
            REQUIRE(path.GetBit(static_cast<uint8_t>(j)) == 1);
        }

        for (int j = p ; j < 256 ; ++j) {
            REQUIRE(path.GetBit(static_cast<uint8_t>(j)) == 0);
        }

        REQUIRE(path.IsPrefixZero(ps[i]));
    }
}

TEST_CASE("test host normalize")
{
    uint64_t v = 0xffffffffffffffffull;
    UInt256 p { v, v, v, v };

    // construct a (host) basekey
    auto hbk = BaseKey { p, BaseKey::LeafDepth / 2 };

    // normalize host key (zero-out unused path bits)
    auto hbk2 = hbk.GetNormalizedKey();
    REQUIRE(hbk == hbk2);
}

TEST_CASE("test proper desc")
{
    uint8_t buf[32];

    for (int i = 0 ; i < 32 ; ++i) {
        buf[i] = i;
    }

    auto h256 = UInt256::Deserialize(buf, sizeof(buf));
    auto v256 = u256_reader({ buf, 32}, 0);

    auto hbk1 = BaseKey { h256, BaseKey::LeafDepth };
    auto hbk2 = BaseKey { h256, BaseKey::LeafDepth / 2 };

    auto vbk1 = Verifier_base_key { v256, BaseKey::LeafDepth };
    auto vbk2 = Verifier_base_key { v256, BaseKey::LeafDepth / 2 };

    REQUIRE(equal(vbk1, hbk1));
    REQUIRE(equal(vbk2, hbk2));
    REQUIRE(is_proper_descendent(Verifier_base_key k0, Verifier_base_key k1)
}
