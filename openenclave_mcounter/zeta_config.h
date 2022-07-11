#pragma once

#define Zeta_VERSION_MAJOR 
#define Zeta_VERSION_MINOR 

/* #undef TRACE_MODE */
/* #undef STATS_MODE */

#ifndef NDEBUG
#define DEBUG
#endif

/* defined to be consistent with the constants in Zeta_Steel_Main.h */
#define VRC_VerificationFailure -1
#define VRC_ParsingFailure 0
#define VRC_AppFailure 1
#define VRC_EntryFailure 2
#define VRC_Success 3
