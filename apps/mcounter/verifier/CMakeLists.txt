configure_file(${APP_COMMON}/config.c.in config.c)

add_library(verifier
            ${DIST_DIR}/ZetaFormats.c
            ${DIST_DIR}/Zeta_Steel_Main.c
            ${DIST_DIR}/krmlinit.c
            ${CMAKE_CURRENT_BINARY_DIR}/config.c)

target_include_directories(verifier
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
    PUBLIC "${APP_HOME}/common"
    PUBLIC ${DIST_DIR}
)

add_subdirectory(test)
