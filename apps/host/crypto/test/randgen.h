#include <cstdint>
#include <cstddef>

namespace Zeta
{
    class RandomGenerator
    {
    public:
        RandomGenerator() = default;

        void Generate(uint8_t *buf, size_t len);

        template<typename T>
        T Generate();

        template<typename T>
        static T GenerateS()
        {
            RandomGenerator rand_gen;
            return rand_gen.Generate<T>();
        }
    };
}
