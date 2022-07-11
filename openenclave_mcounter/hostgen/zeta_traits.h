#pragma once

#include <common.h>
#include <crypt_hash.h>

namespace Zeta
{
    using HashTraits = Blake2Traits;
    using Hasher = CryptoHasher<HashTraits>;
    using HashValue = Hasher::HashValue;

    static const int TransFunctionCount = 3;
    static const int MaxArity = 1;
    static const SlotId StoreSize = 16;
    static const ThreadId ThreadCount = 1;
    static const size_t LogBufSize = (1 << 20);
    static const size_t OutBufSize = (1 << 20);
}
