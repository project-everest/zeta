#include <randgen.h>
#include <stdlib.h>

namespace Zeta
{
    void RandomGenerator::Generate(uint8_t *buf, size_t len)
    {
        for (size_t i = 0 ; i < len ; ++i) {
            buf[i] = static_cast<uint8_t> (rand());
        }
    }

    template<typename T>
    T RandomGenerator::Generate()
    {
        T val;
        Generate(reinterpret_cast<uint8_t*>(&val), sizeof(T));
        return val;
    }
}
