# default hash function is blake2, can be changed using ccmake
set(HASH_FUNCTION "Blake2" CACHE STRING "Hash function")
message (STATUS "Hash function: ${HASH_FUNCTION}")

# Count of application transition functions
SET (FN_COUNT "2" CACHE STRING "Trans function count")
message (STATUS "Transition function count: ${FN_COUNT}")

# Max arity over all transition functions
SET (MAX_ARITY "8" CACHE STRING "Max function arity")
message (STATUS "Max function arity: ${MAX_ARITY}")

SET (LOG_BUF_SIZE "(1 << 20)" CACHE STRING "Log buffer size")
message (LOG_BUF_SIZE "Log buffer size: ${LOG_BUF_SIZE}")

SET (OUT_BUF_SIZE "(1 << 20)" CACHE STRING "Out buffer size")
message (OUT_BUF_SIZE "Log buffer size: ${OUT_BUF_SIZE}")

# host dir
cmake_path(SET HOST_DIR NORMALIZE "${ZETA_HOME}/host/")
message(STATUS "HOST_DIR = ${HOST_DIR}")

configure_file(zeta_traits.h.in zeta_traits.h)
add_subdirectory(crypto)

file(GLOB STUB_SRC
  "src/*.cpp")

add_library(zetastub ${STUB_SRC})

target_include_directories(zetastub
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include/
  PUBLIC ${PROJECT_BINARY_DIR}
  PUBLIC ${PROJECT_BINARY_DIR}/apps/host
)

target_link_libraries(zetastub
  PUBLIC crypto
  PRIVATE fmt::fmt)

add_subdirectory(test)
