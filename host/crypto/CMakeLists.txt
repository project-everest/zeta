#----------------------------------------------------------------------
# Library

# Library sources
file(GLOB LIB_SRC
    "src/*.cpp"
)

SET (HACL_BLAKE_OBJS
     ${HACL_DIR}/gcc-compatible/Hacl_Blake2b_32.o
     ${HACL_DIR}/gcc-compatible/Lib_Memzero0.o)

add_custom_command(
  OUTPUT ${HACL_BLAKE_OBJS}
  WORKING_DIRECTORY ${HACL_DIR}/gcc-compatible/
  COMMAND echo `pwd`
  COMMAND ./configure --disable-ocaml
  COMMAND make ${HACL_BLAKE_OBJS})

# Crypto library
add_library(crypto ${LIB_SRC} ${HACL_BLAKE_OBJS})

target_include_directories(crypto
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include
  PUBLIC ${DIST_DIR}
  PRIVATE ${PROJECT_BINARY_DIR}
  PRIVATE ${HACL_DIR}/gcc-compatible/
  PRIVATE ${HACL_DIR}/kremlin/include
)

target_link_libraries(crypto
  PRIVATE fmt::fmt)
