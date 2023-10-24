

#include "krmlinit.h"

#include "internal/Zeta_Steel_SafeMain.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void)
{
  Zeta_Steel_AEADHandle_aead_handle = Zeta_Steel_AEADHandle_init_aead_handle();
  Zeta_Steel_Main_top_level_state *r2_state = Zeta_Steel_Main_init();
  Zeta_Steel_SafeMain_Handle_handle = r2_state;
}

