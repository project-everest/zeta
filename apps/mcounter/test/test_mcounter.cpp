#include <app.h>
#include <verifier_stub.h>

using TransFn = Zeta::AppTransFn;
using Record = Zeta::mcounter::Record;
using New = Zeta::mcounter::New;
using VerifierStub = Zeta::VerifierStub;

void OutputCallback (const TransFn *fn, const uint8_t *buf, size_t len)
{

}

int main(int argc, char *argv[])
{
    VerifierStub verifier { 0, OutputCallback };

    Record r { 0 };
    New newCounter { 0, r };
    verifier.Run(&newCounter);
    verifier.Flush();

    return 0;
}
