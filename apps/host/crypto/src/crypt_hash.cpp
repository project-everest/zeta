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
#include <Hacl_Blake2b_32.h>

#include <stdio.h>

static void PrintHex(uint8_t c)
{
    printf("%02hhx", c);
}

static void PrintHex(const uint8_t* mesg, size_t len)
{
    for (size_t i = 0 ; i < len ; ++i) {
        PrintHex(mesg[i]);
    }
}

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
        PrintHex(mesg.data(), mesg.size());
        blake2b_update(&state_, mesg.data(), mesg.size());       
    }

    void Blake2Hasher::HashFinal(HashValue& hashValue)
    {
        printf(" ==> ");
        blake2b_final(&state_, hashValue.Bytes(), HashSize);
        PrintHex((const uint8_t*)hashValue.Bytes(), HashSize);
        printf("\n");
        Init();
    }
}
