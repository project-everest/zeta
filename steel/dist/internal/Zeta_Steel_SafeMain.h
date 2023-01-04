

#ifndef __internal_Zeta_Steel_SafeMain_H
#define __internal_Zeta_Steel_SafeMain_H

#include "krmllib.h"


#include "../Zeta_Steel_SafeMain.h"
#include "steel_atomics.h"
#include "zeta_application.h"
EverCrypt_AEAD_state_s *Zeta_Steel_AEADHandle_init_aead_handle();

extern EverCrypt_AEAD_state_s *Zeta_Steel_AEADHandle_aead_handle;

typedef struct Zeta_Steel_Main_top_level_state_s Zeta_Steel_Main_top_level_state;

Zeta_Steel_Main_top_level_state *Zeta_Steel_Main_init();

typedef Zeta_Steel_Main_top_level_state *Zeta_Steel_SafeMain_Handle_state_t;

extern Zeta_Steel_SafeMain_Handle_state_t Zeta_Steel_SafeMain_Handle_handle;


#define __internal_Zeta_Steel_SafeMain_H_DEFINED
#endif
