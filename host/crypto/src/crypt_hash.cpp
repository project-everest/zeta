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
        for (int i = 0 ; i < StateSize64 ; ++i) {
            wv_[i] = hash_[i] = 0ull;
        }
        prev_ = FStar_UInt128_uint64_to_uint128(0ull);
        Hacl_Blake2b_32_blake2b_init(wv_, hash_, 0, nullptr, HashSize);

        memset(block_, 0, sizeof(block_));
        filled_ = 0;
        len_ = 0;
    }

    Blake2Hasher::CryptoHasher()
        : filled_ { 0 }
        , len_ { 0 }
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
        const uint8_t* data = mesg.data();
        size_t len = mesg.size();
        len_ += len;

        assert(filled_ <= BlockSize);

        auto to_fill = (filled_ + len > BlockSize)?
            (BlockSize - filled_) :
            len;

        memcpy(block_ + filled_, data, to_fill);
        data += to_fill;
        len -= to_fill;
        filled_ += to_fill;

        if (filled_ < BlockSize || len == 0) {
            return;
        }

        Hacl_Blake2b_32_blake2b_update_multi(BlockSize, wv_, hash_, prev_, block_, 1);
        memset(block_, 0, sizeof(block_));
        filled_ = 0;

        auto nb = (len - 1) / BlockSize;
        if (nb > 0) {
            Hacl_Blake2b_32_blake2b_update_multi(0 /* not used */,
                                                 wv_,
                                                 hash_,
                                                 prev_,
                                                 const_cast<uint8_t*>(data),
                                                 nb);
            data += nb * BlockSize;
            assert (len > nb * BlockSize);
            len -= nb * BlockSize;
        }

        memcpy(block_, data, len);
        filled_ = len;
    }

    void Blake2Hasher::HashFinal(HashValue& hashValue)
    {
        Hacl_Blake2b_32_blake2b_update_last(len_, wv_, hash_, prev_, filled_,
                                            /* hacky workaround to make it streaming */
                                            block_ - len_ + filled_);
        
        Hacl_Blake2b_32_blake2b_finish(HashSize,
                                       reinterpret_cast<uint8_t*>(hashValue.Bytes()),
                                       hash_);
        Init();
    }
}
