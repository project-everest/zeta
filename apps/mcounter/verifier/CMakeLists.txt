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

find_program(MAKE_EXE make)

add_custom_command(
  OUTPUT ${APP_FORMATS_DIR}/out/App_key.c ${APP_FORMATS_DIR}/out/App_val.c
  WORKING_DIRECTORY ${APP_FORMATS_DIR}
  COMMAND ${MAKE_EXE})

add_library(verifier
            ${DIST_DIR}/ZetaFormats.c
            ${DIST_DIR}/krmlinit.c
            ${CMAKE_CURRENT_BINARY_DIR}/config.c
            ${HACL_BLAKE_OBJS}
            app.c
            ${APP_FORMATS_DIR}/out/App_key.c
            ${APP_FORMATS_DIR}/out/App_val.c
            ${APP_COMMON}/formats.c
            )

target_include_directories(verifier
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
    PUBLIC "${APP_HOME}/common"
    PUBLIC ${DIST_DIR}
    PUBLIC ${APP_FORMATS_DIR}/out
)

add_subdirectory(test)
