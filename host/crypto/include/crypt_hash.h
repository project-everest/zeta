#pragma once

//*********************************************************************************************
//          Copyright (c) Microsoft Corporation
//
//  @File crypt_hash.h
//
//  Purpose: Provide cryptographic hasher class
//
//*********************************************************************************************

#include <zeta_config.h>
#include <cstdint>
#include <fmt/format.h>
#include <gsl/span>
#include <Hacl_Blake2b_32.h>

namespace Zeta
{
    template<typename HashTraits>
    class CryptoHasher;

    template<int Size64>
    class THashValue;

    template<>
    class THashValue<4>
    {
    public:

        THashValue()
        {
            hash_[0] = hash_[1] = hash_[2] = hash_[3] = 0;
        }

        THashValue(const THashValue& other) = default;
        THashValue& operator=(const THashValue& other) = default;

        const uint64_t (&Bytes () const) [4]
        {
            return hash_;
        }

        uint64_t (&Bytes()) [4]
        {
            return hash_;
        }

        bool operator == (const THashValue& other) const
        {
            return hash_[0] == other.hash_[0] &&
                   hash_[1] == other.hash_[1] &&
                   hash_[2] == other.hash_[2] &&
                   hash_[3] == other.hash_[3];
        }

        bool operator != (const THashValue& other) const
        {
            return !(*this == other);
        }

        uint64_t* Serialize(uint64_t* buf) const
        {
            auto phash = hash_;
            *buf++ = *phash++;
            *buf++ = *phash++;
            *buf++ = *phash++;
            *buf++ = *phash++;

            return buf;
        }

#ifdef TRACE_MODE

        std::string GetFormattedSelf() const
        {
            return fmt::format("0x{:016x}-{:016x}-{:016x}-{:016x}",
                               hash_[0], hash_[1], hash_[2], hash_[3]);
        }

#endif

    private:
        uint64_t hash_[4];
    };

    template<typename HashTraits>
    class CryptoHasher;

    struct Blake2Traits
    {
        static const int HashSize = 32;
        static const int HashSize64 = HashSize / 8;
    };

    template<>
    class CryptoHasher<Blake2Traits>
    {
    public:
        using HashTraits = Blake2Traits;
        using HashValue = THashValue<Blake2Traits::HashSize64>;

        CryptoHasher();

        CryptoHasher(const CryptoHasher&) = delete;
        CryptoHasher& operator=(const CryptoHasher&) = delete;
        CryptoHasher(CryptoHasher&&) = default;

        static const int HashSize = HashTraits::HashSize;

        void Hash(gsl::span<const uint8_t> mesg, HashValue& hashBuf);

        template<typename T>
        void HashPartialT(const T& val)
        {
            HashPartial(gsl::span<const uint8_t>(reinterpret_cast<const uint8_t*>(&val), sizeof(T)));
        }

        void HashPartial(gsl::span<const uint8_t> mesg);
        void HashFinal(HashValue& hashBuf);

    private:
        void Init();

        static const int StateSize = 128;
        static const int BlockSize = 128;
        static const int StateSize64 = StateSize / sizeof(uint64_t);
        uint64_t wv_ [StateSize64];
        uint64_t hash_ [StateSize64];
        FStar_UInt128_uint128 prev_;
        uint8_t block_ [BlockSize];
        int filled_;
    };

    using Blake2Hasher = CryptoHasher<Blake2Traits>;
}
