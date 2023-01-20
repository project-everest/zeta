

#ifndef __krmlinit_H
#define __krmlinit_H

#include "krmllib.h"



#include "steel_atomics.h"
#include "zeta_application.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif


void krmlinit_globals(void);


#define __krmlinit_H_DEFINED
#endif
