configure_file ("${DIST_DIR}/ZetaFormats.c" ZetaFormats.c COPYONLY)
configure_file ("${DIST_DIR}/ZetaFormats.h" ZetaFormats.h COPYONLY)
configure_file ("${DIST_DIR}/Zeta_Steel_Main.c" Zeta_Steel_Main.c COPYONLY)
configure_file ("${DIST_DIR}/kremlinit.c" kremlinit.c COPYONLY)

add_library(verifier
            ${CMAKE_CURRENT_BINARY_DIR}/ZetaFormats.c
            ${CMAKE_CURRENT_BINARY_DIR}/Zeta_Steel_Main.c
            ${CMAKE_CURRENT_BINARY_DIR}/kremlinit.c)
