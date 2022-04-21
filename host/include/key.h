#pragma once

#include <assert.h>
#include <stdint.h>
#include <memory>
#include <trace.h>

namespace Zeta
{
    //----------------------------------------------------------------------
    // class: UInt256
    //
    // a 256 bit value
    //
    class alignas(8) UInt256
    {
    public:
        UInt256 () = default;

        UInt256 (int ival)
        {
            bytes_[0] = ival;
            bytes_[1] = bytes_[2] = bytes_[3] = 0;
        }

        UInt256 (uint64_t ui64val)
        {
            bytes_[0] = ui64val;
            bytes_[1] = bytes_[2] = bytes_[3] = 0;
        }

        UInt256 (uint64_t b0, uint64_t b1, uint64_t b2, uint64_t b3)
        {
            bytes_[0] = b0;
            bytes_[1] = b1;
            bytes_[2] = b2;
            bytes_[3] = b3;
        }

        bool operator == (const UInt256& v) const
        {
            return bytes_[0] == v.bytes_[0] &&
                   bytes_[1] == v.bytes_[1] &&
                   bytes_[2] == v.bytes_[2] &&
                   bytes_[3] == v.bytes_[3];
        }

        static uint16_t GetLargestCommonPrefixSize(const UInt256& v1, const UInt256& v2)
        {
            for (uint8_t i = 0 ; i < 4 ; ++i)
            {
                if (v1.bytes_[i] != v2.bytes_[i])
                {
                    return (i << 6) + __builtin_clzll(v1.bytes_[i] ^ v2.bytes_[i]);
                }
            }

            return 256;
        }

        uint8_t GetBit(uint8_t p) const
        {
            uint8_t n = p >> 6;
            assert (n < 4);

            uint8_t s = 63 - (p & 0x3f);
            return (bytes_[n] >> s) & 0x01;
        }

        void SetBit(uint8_t p)
        {
            uint8_t n = p >> 6;
            assert (n < 4);

            uint8_t s = 63 - (p & 0x3f);
            bytes_[n] |= (1ull << s);
        }

        void ClearBit(uint8_t p)
        {
            uint8_t n = p >> 6;
            assert (n < 4);

            uint8_t s = 63 - (p & 0x3f);
            bytes_[n] &= (~1ull << s);
        }

        void ZeroSuffix(uint64_t size)
        {
            assert(size <= 256);

            auto n = (size >> 6);
            assert(n <= 4);

            for (auto i = 4 - n ; i < 4 ; ++i) {
                bytes_[i] = 0;
            }

            if (n < 4) {
                auto i = 3 - n;
                auto s = (size & 0x3f);
                assert(s < 64);
                bytes_[i] &= (~0ull << s);
            }
        }

        bool IsSuffixZero(uint64_t size) const
        {
            assert(size <= 256);

            auto n = (size >> 6);
            assert(n <= 4);

            for (auto i = 4 - n ; i < 4 ; ++i) {
                if (bytes_[i] != 0) {
                    return false;
                }
            }

            if (n < 4) {
                auto i = 3 - n;
                auto s = (size & 0x3f);
                assert(s < 64);
                if ((bytes_[i] & ~(~0ull << s)) != 0) {
                    return false;
                }
            }

            return true;
        }

        uint64_t* Serialize(uint64_t* buf) const
        {
            const uint64_t* pbytes = bytes_;
            *buf++ = *pbytes++;
            *buf++ = *pbytes++;
            *buf++ = *pbytes++;
            *buf++ = *pbytes++;

            return buf;
        }

        const uint64_t* Bytes() const
        {
            return bytes_;
        }

        uint64_t* Bytes()
        {
            return bytes_;
        }

#ifdef TRACE_MODE

        std::string GetFormattedSelf() const
        {
            return fmt::format("0x{:016x}-{:016x}-{:016x}-{:016x}",
                               bytes_[0], bytes_[1], bytes_[2], bytes_[3]);
        }

#endif

    private:

        uint64_t bytes_[4];
    };

    static_assert(sizeof(UInt256) == 32);

    enum class DescDir: uint8_t
    {
        Left = 0,
        Right = 1
    };

    class DescDirTr
    {
    public:
        static DescDir Other(DescDir d)
        {
            return static_cast<DescDir>(1 - static_cast<uint8_t>(d));
        }

        static uint8_t ToByte(DescDir d)
        {
            return static_cast<uint8_t>(d);
        }
    };

    //--------------------------------------------------------------------------------
    // BaseKey
    //
    // Base key identifies a location in the sparse merkle tree
    //
    class BaseKey
    {
    public:
        static const uint16_t LeafDepth = sizeof(UInt256) * 8;

        BaseKey(UInt256 path, uint16_t depth)
            : path_ { path }
            , depth_ { depth }
        {
            assert (depth_ <= LeafDepth);
        }

        BaseKey()
            : path_ { 0 }
            , depth_ { 0 }
        {

        }

        bool operator == (const BaseKey& other) const
        {
            if (other.GetDepth() != GetDepth())
            {
                return false;
            }

            return UInt256::GetLargestCommonPrefixSize(path_, other.path_) >= depth_;
        }

        bool operator != (const BaseKey& other) const
        {
            return !(*this == other);
        }

        uint16_t GetDepth() const
        {
            return depth_;
        }

        const UInt256& GetPath() const
        {
            return path_;
        }

        bool IsRoot() const { return 0 == GetDepth(); }

        bool IsLeaf() const { return LeafDepth == GetDepth(); }

        // Am I a proper ancestor of other
        bool IsAncestor (const BaseKey& other) const
        {
            if (other.GetDepth() <= GetDepth())
            {
                return false;
            }

            return UInt256::GetLargestCommonPrefixSize(path_, other.path_) >= depth_;
        }

        // Am I a proper descendant of ancAddr
        bool IsDescendant (const BaseKey& other) const
        {
            return other.IsAncestor(*this);
        }

        // Get the descendant direction (Left|Right)
        DescDir GetDescDir (const BaseKey& desc) const
        {
            assert(IsAncestor(desc));
            assert(GetDepth() < 256);
            return static_cast<DescDir>(desc.path_.GetBit(GetDepth()));
        }

        static BaseKey GetLeafKey(const UInt256& path)
        {
            return BaseKey { path, LeafDepth };
        }

        static BaseKey GetLeastCommonAncestor(const BaseKey& a1, const BaseKey& a2)
        {
            auto d = UInt256::GetLargestCommonPrefixSize(a1.path_, a2.path_);
            d = std::min(d, a1.GetDepth());
            d = std::min(d, a2.GetDepth());
            auto ret = BaseKey{a1.path_, d};
            ret.path_.ZeroSuffix(LeafDepth - d);
            return ret;
        }

        bool IsNormalized() const
        {
            auto height = LeafDepth - depth_;
            return path_.IsSuffixZero(height);
        }

        bool operator < (const BaseKey& other) const
        {
            // min depth
            auto d = std::min(GetDepth(), other.GetDepth());

            auto p1 = GetPath().Bytes();
            auto p2 = other.GetPath().Bytes();

            // number of uint64_t to compare
            auto n64 = d >> 6;
            assert(n64 <= 4);

            for (int i = 0 ; i < n64 ; ++i)
            {
                if (p1[i] != p2[i])
                {
                    return (p1[i] < p2[i]);
                }
            }

            if (n64 == 4)
            {
                // equal
                return false;
            }

            assert(n64 < 4);
            auto nb = d & 0x3f;
            uint64_t mask = ~(~0ull >> nb);

            auto dw1 = p1[n64] & mask;
            auto dw2 = p2[n64] & mask;

            return dw1 < dw2 || dw1 == dw2 && GetDepth() < other.GetDepth();
        }


#ifdef TRACE_MODE

        std::string GetFormattedSelf() const
        {
            return fmt::format("{}##{}", path_.GetFormattedSelf(), depth_);
        }

#endif

        static BaseKey Root;

    private:

        UInt256 path_;
        uint16_t depth_;
    };
}

#ifdef TRACE_MODE

std::ostream& operator<< (std::ostream&, const Zeta::UInt256&);
std::ostream& operator<<(std::ostream &os, const Zeta::BaseKey&);

#endif
