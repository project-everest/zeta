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

    void Blake2Hasher::Hash(const uint8_t *mesg, size_t mesgLen, HashValue& hashBuf)
    {
        blake2b(reinterpret_cast<uint8_t*>(hashBuf.Bytes()),
                HashSize,
                mesg,
                mesgLen,
                nullptr,
                0);
    }

    void Blake2Hasher::HashPartial(const uint8_t *mesg, size_t mesgLen)
    {
        blake2b_update(&state_, mesg, mesgLen);
    }

    void Blake2Hasher::HashFinal(HashValue& hashValue)
    {
        blake2b_final(&state_, hashValue.Bytes(), HashSize);
        Init();
    }
}
