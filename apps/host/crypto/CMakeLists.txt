#----------------------------------------------------------------------
# Library

# Library sources
file(GLOB LIB_SRC
    "src/*.cpp"
    "src/*.c"
)

# Crypto library
add_library(crypto ${LIB_SRC})

target_include_directories(crypto
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include
  PUBLIC ${PROJECT_BINARY_DIR}
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
