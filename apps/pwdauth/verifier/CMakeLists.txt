configure_file ("${DIST_DIR}/ZetaFormats.c" ZetaFormats.c COPYONLY)
configure_file ("${DIST_DIR}/ZetaFormats.h" ZetaFormats.h COPYONLY)
configure_file ("${DIST_DIR}/Zeta_Steel_Main.c" Zeta_Steel_Main.c COPYONLY)
configure_file ("${DIST_DIR}/Zeta_Steel_Main.h" Zeta_Steel_Main.h COPYONLY)
configure_file ("${DIST_DIR}/kremlinit.c" kremlinit.c COPYONLY)

add_library(verifier
            ${CMAKE_CURRENT_BINARY_DIR}/ZetaFormats.c
            ${CMAKE_CURRENT_BINARY_DIR}/Zeta_Steel_Main.c
            ${CMAKE_CURRENT_BINARY_DIR}/kremlinit.c)

target_include_directories(verifier
    PUBLIC "$ENV{EVERPARSE_HOME}/include"
    PUBLIC "$ENV{EVERPARSE_HOME}/kremlib/dist/minimal"
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
    PUBLIC "${APP_HOME}/common"
)
