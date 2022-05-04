#include <appcommon.h>
#include <zeta_traits.h>

using namespace Zeta;

BaseKey AppKey::GetBaseKey() const
{
    HashValue hashValue;
    Hasher hasher{};
    Serialize4Hash(hasher);
    hasher.HashFinal(hashValue);

    auto hashBytes = hashValue.Bytes();

    auto path = UInt256 { hashBytes[0], hashBytes[1], hashBytes[2], hashBytes[3] };
    return BaseKey { path, BaseKey::LeafDepth };
}

AppTransFn::AppTransFn(uint8_t id, int arity, bool hasOutput)
    : id_ { id }
    , arity_ { arity }
    , hasOutput_ { hasOutput }
{

}
