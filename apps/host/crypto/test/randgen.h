#include <gsl/span>

namespace Zeta
{
    class RandomGenerator
    {
    public:
        RandomGenerator() = default;

        void Generate(gsl::span<uint8_t> buf);

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
