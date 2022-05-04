#include <app.h>
#include <verifier_stub.h>
#include <Zeta_Steel_Main.h>

using TransFn = Zeta::AppTransFn;
using Record = Zeta::mcounter::Record;
using New = Zeta::mcounter::New;
using VerifierStub = Zeta::VerifierStub;

typedef FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result zeta_res_t;
typedef Zeta_Steel_Main_top_level_state top_state_t;




void OutputCallback (const TransFn *fn, const uint8_t *buf, size_t len)
{

}



int main(int argc, char *argv[])
{
  /*
  VerifierStub verifier { 0, OutputCallback };

  Record r { 0 };
  New newCounter { 0, r };
  verifier.Run(&newCounter);
  verifier.Flush();
  */

    return 0;
}
