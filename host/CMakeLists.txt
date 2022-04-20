set(HASH_FUNCTION "Blake2" CACHE STRING "Hash function")
message (STATUS "Hash function: ${HASH_FUNCTION}")

configure_file(zeta_traits.h.in zeta_traits.h)
add_subdirectory(crypto)
