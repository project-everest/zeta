//*********************************************************************************************
//          Copyright (c) Microsoft Corporation
//
//  @File crypt_hash.cpp
//
//  Purpose: Implement cryptographic hasher class
//
//*********************************************************************************************

#include <crypt_hash.h>
#include <cstddef>
#include <cassert>
#include <cstdint>

namespace Zeta
{
    void Blake2Hasher::Init()
    {
        blake2b_init(&state_, HashSize);
    }

    Blake2Hasher::CryptoHasher()
    {
        Init();
    }

    void Blake2Hasher::Hash(gsl::span<const uint8_t> mesg, HashValue& hashBuf)
    {
        Hacl_Blake2b_32_blake2b(HashSize,
                                reinterpret_cast<uint8_t*>(hashBuf.Bytes()),
                                mesg.size(),
                                const_cast<uint8_t*>(mesg.data()),
                                0,
                                nullptr);
    }

    void Blake2Hasher::HashPartial(gsl::span<const uint8_t> mesg)
    {
        blake2b_update(&state_, mesg.data(), mesg.size());       
    }

    void Blake2Hasher::HashFinal(HashValue& hashValue)
    {
        blake2b_final(&state_, hashValue.Bytes(), HashSize);
        Init();
    }
}
