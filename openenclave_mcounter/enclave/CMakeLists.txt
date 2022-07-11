# Copyright (c) Open Enclave SDK contributors.
# Licensed under the MIT License.

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_subdirectory(verifier)

# Use the edger8r to generate C bindings from the EDL file.
add_custom_command(
  OUTPUT openenclave_mcounter_t.h openenclave_mcounter_t.c openenclave_mcounter_args.h
  DEPENDS ${CMAKE_SOURCE_DIR}/openenclave_mcounter.edl
  COMMAND
    openenclave::oeedger8r --trusted ${CMAKE_SOURCE_DIR}/openenclave_mcounter.edl
    --search-path ${OE_INCLUDEDIR} --search-path
    ${OE_INCLUDEDIR}/openenclave/edl/sgx)

add_executable(enclave enc.c ${CMAKE_CURRENT_BINARY_DIR}/openenclave_mcounter_t.c)

if (WIN32)
  maybe_build_using_clangw(enclave)
endif ()


# option(BUILD_SHARED_LIBS "Build using shared libraries" ON)

target_compile_definitions(enclave PUBLIC OE_API_VERSION=2)

# Need for the generated file openenclave_mcounter_t.h
target_include_directories(enclave PRIVATE ${CMAKE_CURRENT_BINARY_DIR})

if (LVI_MITIGATION MATCHES ControlFlow)
  # Helper to enable compiler options for LVI mitigation.
  apply_lvi_mitigation(enclave)
  # Link against LVI-mitigated libraries.
  target_link_libraries(
    enclave openenclave::oeenclave-lvi-cfg
    openenclave::oecrypto${OE_CRYPTO_LIB}-lvi-cfg openenclave::oelibc-lvi-cfg mcounter-verifier)
else ()
  target_link_libraries(
    enclave openenclave::oeenclave openenclave::oecrypto${OE_CRYPTO_LIB}
    openenclave::oelibc mcounter-verifier)
endif ()
