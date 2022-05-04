configure_file(${APP_VERIFIER}/config.c.in config.c)

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
            ${DIST_DIR}/krmlinit.c
            ${CMAKE_CURRENT_BINARY_DIR}/config.c
            ${HACL_BLAKE_OBJS}
            app.c
            ${APP_VERIFIER}/formats.c
            )

target_include_directories(verifier
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
    PUBLIC ${APP_VERIFIER}
    PUBLIC ${DIST_DIR}
    PUBLIC ${APP_FORMATS_DIR}
)

target_link_libraries(verifier
  PRIVATE format)

add_subdirectory(test)
