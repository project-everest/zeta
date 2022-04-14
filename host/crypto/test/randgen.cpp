#include <randgen.h>
#include <stdlib.h>

namespace Zeta
{
    void RandomGenerator::Generate(gsl::span<uint8_t> buf)
    {
        for (size_t i = 0 ; i < buf.size() ; ++i) {
            buf[i] = static_cast<uint8_t> (rand());
        }
    }

    template<typename T>
    T RandomGenerator::Generate()
    {
        T val;
        Generate(gsl::span(reinterpret_cast<uint8_t*>(&val), sizeof(T)));
        return val;
    }
}
