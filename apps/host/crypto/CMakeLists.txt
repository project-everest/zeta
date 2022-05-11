#----------------------------------------------------------------------
# Library

# Library sources
file(GLOB LIB_SRC
    "src/*.cpp"
    "src/*.c"
)

SET (HACL_BLAKE_OBJS
     ${HACL_DIR}/gcc-compatible/Hacl_Blake2b_32.o
     ${HACL_DIR}/gcc-compatible/Lib_Memzero0.o
)

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
  PUBLIC ${PROJECT_BINARY_DIR}
  PUBLIC ${HACL_DIR}/gcc-compatible/
  PUBLIC ${HACL_DIR}/kremlin/include
)

target_link_libraries(crypto
  PUBLIC fmt::fmt)

#----------------------------------------------------------------------
# Crypto test

# Test sources
file(GLOB TEST_SRC
  "test/*.cpp"
)

add_executable(cryptotest ${TEST_SRC})

target_link_libraries(cryptotest
  PRIVATE crypto
  PRIVATE Microsoft.GSL::GSL
  PRIVATE fmt::fmt
  PRIVATE Catch2::Catch2
)

target_include_directories(cryptotest
  PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/test
)

include(CTest)
include(Catch)
catch_discover_tests(cryptotest)
