configure_file(${APP_COMMON}/config.c.in config.c)

SET (HACL_BLAKE_OBJS
     ${HACL_DIR}/gcc-compatible/Hacl_Blake2b_32.o
     ${HACL_DIR}/gcc-compatible/Lib_Memzero0.o)

add_custom_command(
  OUTPUT ${HACL_BLAKE_OBJS}
  WORKING_DIRECTORY ${HACL_DIR}/gcc-compatible/
  COMMAND echo `pwd`
  COMMAND ./configure --disable-ocaml
  COMMAND make ${HACL_BLAKE_OBJS})

add_library(verifier
            ${DIST_DIR}/ZetaFormats.c
            ${DIST_DIR}/Zeta_Steel_Main.c
            ${DIST_DIR}/krmlinit.c
            ${CMAKE_CURRENT_BINARY_DIR}/config.c
            ${HACL_BLAKE_OBJS})

target_include_directories(verifier
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
    PUBLIC "${APP_HOME}/common"
    PUBLIC ${DIST_DIR}
)

add_subdirectory(test)
