#include <cstdint>
#define CATCH_CONFIG_MAIN
#include <catch2/catch.hpp>

#include <crypt_hash.h>
#include <randgen.h>

#include <iostream>

using namespace Zeta;

static uint8_t GetNibble(char c)
{
    if (c <= '9') {
        assert(c >= '0');
        return (c - '0');
    }

    assert(c >= 'a' && c <= 'f');
    return 10 + (c - 'a');
}

static uint8_t GetByte(char mc, char lc)
{
    return (GetNibble(mc) << 4) + GetNibble(lc);
}

static Blake2HashValue DecodeHash(const char* encHash)
{
    Blake2HashValue hv;
    auto hashBytes = reinterpret_cast<uint8_t*>(hv.Bytes());

    assert(strlen(encHash) == 64);
    const char *c = encHash;

    for (int i = 0 ; i < Blake2Traits::HashSize ; ++i) {
        auto b = GetByte(*c, *(c+1));
        hashBytes[i] = b;
        c += 2;
    }

    return hv;
}

TEST_CASE("test blake2")
{
    Blake2Hasher hasher;
    RandomGenerator randGen;

    SECTION("test published string")
    {
        static const int MesgSize = 3;
        uint8_t mesg [MesgSize];

        mesg[0] = 'a';
        mesg[1] = 'b';
        mesg[2] = 'c';
        Blake2HashValue hash;

        hasher.Hash(mesg, hash);

        auto expHashEnc = "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319";
        auto expHash = DecodeHash(expHashEnc);

        REQUIRE(hash == expHash);
    }

    SECTION("test published string (incremental)")
    {
        static const int MesgSize = 3;
        uint8_t mesg [MesgSize];

        mesg[0] = 'a';
        mesg[1] = 'b';
        mesg[2] = 'c';
        Blake2HashValue hash;

        hasher.HashPartial(gsl::span<const uint8_t>(mesg, 1));
        hasher.HashPartial(gsl::span<const uint8_t>(mesg + 1, 1));
        hasher.HashPartial(gsl::span<const uint8_t>(mesg + 2, 1));
        hasher.HashFinal(hash);

        auto expHashEnc = "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319";
        auto expHash = DecodeHash(expHashEnc);

        REQUIRE(hash == expHash);
    }

    SECTION("test full/incremental consistency")
    {
        static const int MaxMesgSize = 1024;
        uint8_t mesg [MaxMesgSize];
        Blake2HashValue hash1, hash2;

        randGen.Generate(mesg);

        for (int i = 1 ; i <= 1024 ; ++i) {
            hasher.Hash(gsl::span<const uint8_t>(mesg, i), hash1);

            for (int j = 0 ; j < i ; ++j) {
                hasher.HashPartial(gsl::span<const uint8_t>(mesg + j, 1));
            }

            hasher.HashFinal(hash2);
            REQUIRE(hash1 == hash2);
        }
    }
}
