#pragma once

#include <cassert>
#include <cstdint>
#include <limits>

#ifndef NDEBUG
#define DEBUG
#endif

namespace Zeta
{
    // Verified operation identifiers
    using VOpId = uint16_t;

    // Verifier cache index (location)
    using SlotId = uint16_t;

    static const SlotId InvalidSlotId = std::numeric_limits<SlotId>::max();

    // Thread ids for multiple concurrent log streams
    using ThreadId = uint8_t;

    // Invalid thread id
    static const ThreadId InvalidThreadId = std::numeric_limits<ThreadId>::max();

    // Epoch ids for blum deferred verification
    using EpochId = uint16_t;

    static const EpochId InvalidEpochId = std::numeric_limits<EpochId>::max();

    // Timestamp used for blum protocol
    //
    // The 64 bits of timestamp encodes the following information:
    // < ProcId (8 bits), EpochId (16 bits), Counter (40 bits)>
    //
    using Timestamp = uint64_t;

    static const Timestamp InvalidTimestamp = std::numeric_limits<Timestamp>::max();

    // Counter field within a timestamp
    using Counter = uint64_t;

    static const Counter CounterMask = 0x000000ffffffffffull;
    static const Counter InvalidCounter = CounterMask;
    static const Counter CounterZero = ~CounterMask;

    // Timestamp traits
    //
    // Helper methods to construct and deconstruct timestamps
    //
    struct TimestampTr
    {
        // Get the epoch from a timestamp
        static EpochId GetEpoch(Timestamp t)
        {
            return static_cast<EpochId>((t >> 40) & 0x000000000000ffffull);
        }

        // Get the procid from a timestamp
        static ThreadId GetThread(Timestamp t)
        {
            return static_cast<ThreadId>(t >> 56);
        }

        // Get the counter from a timestamp
        static Counter GetCounter(Timestamp t)
        {
            return (t & CounterMask);
        }

        // Construct a timestamp from its constituents
        static Timestamp GetTimestamp(EpochId epoch, ThreadId thread, Counter counter) {
            Timestamp t = thread;

            t <<= 16;
            t |= epoch;

            t <<= 40;
            t |= counter;

            return t;
        }

        static Timestamp GetInitClock(EpochId epochId)
        {
            Timestamp t = epochId;
            t <<= 40;
            return t;
        }

        static Timestamp GetClock(Timestamp t)
        {
            return (t & 0x00ffffffffffffffull);
        }

        static Timestamp GetTimestamp(ThreadId threadId, Timestamp clock)
        {
            Timestamp t = threadId;

            t <<= 56;
            t |= clock;

            return t;
        }

        static const Timestamp EpochMask = 0x00ffff0000000000ull;
        static const Timestamp EpochReset = ~EpochMask;

        static Timestamp NextEpoch(Timestamp t)
        {
            Timestamp epoch = GetEpoch(t) + 1;

            t &= EpochReset;  // Zero out the epoch
            assert(GetEpoch(t) == 0);

            epoch <<= 40;
            t |= epoch;

            return t;
        }
    };

    // Cache alignment
    static const int CacheAlign = 64;
}
