

#ifndef __internal_Zeta_Steel_SafeMain_H
#define __internal_Zeta_Steel_SafeMain_H

#include "krmllib.h"

#include "../Zeta_Steel_SafeMain.h"
#include "steel_atomics.h"
#include "zeta_application.h"

EverCrypt_AEAD_state_s *FStar_Pervasives_false_elim__Zeta_Steel_AEADHandle_aead_handle_t(void);

EverCrypt_AEAD_state_s *Zeta_Steel_AEADHandle_init_aead_handle(void);

extern EverCrypt_AEAD_state_s *Zeta_Steel_AEADHandle_aead_handle;

typedef struct Zeta_Steel_Main_thread_state_s Zeta_Steel_Main_thread_state;

typedef struct Zeta_Steel_Main_top_level_state_s Zeta_Steel_Main_top_level_state;

void
Zeta_Steel_Main_init_all_threads_state(Zeta_Steel_Main_thread_state *all_threads, uint16_t i);

Zeta_Steel_Main_top_level_state *Zeta_Steel_Main_init(void);

typedef Zeta_Steel_Main_top_level_state *Zeta_Steel_SafeMain_Handle_state_t;

extern Zeta_Steel_SafeMain_Handle_state_t Zeta_Steel_SafeMain_Handle_handle;


#define __internal_Zeta_Steel_SafeMain_H_DEFINED
#endif
