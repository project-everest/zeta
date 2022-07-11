# Copyright (c) Open Enclave SDK contributors.
# Licensed under the MIT License.

file(GLOB SRC
  "*.cpp" "*.c")

add_custom_command(
  OUTPUT openenclave_mcounter_u.h openenclave_mcounter_u.c openenclave_mcounter_args.h
  DEPENDS ${CMAKE_SOURCE_DIR}/openenclave_mcounter.edl
  COMMAND
    openenclave::oeedger8r --untrusted ${CMAKE_SOURCE_DIR}/openenclave_mcounter.edl
    --search-path ${OE_INCLUDEDIR} --search-path
    ${OE_INCLUDEDIR}/openenclave/edl/sgx)



add_executable(openenclave_mcounter_host host.cpp 
			       ${SRC}
                               ${CMAKE_CURRENT_BINARY_DIR}/openenclave_mcounter_u.c)

if (WIN32)
  copy_oedebugrt_target(openenclave_mcounter_host_oedebugrt)
  add_dependencies(openenclave_mcounter_host openenclave_mcounter_host_oedebugrt)
endif ()

target_include_directories(
  openenclave_mcounter_host # Needed for the generated file openenclave_mcounter_u.h
		PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
                          ${CMAKE_CURRENT_BINARY_DIR})

target_link_libraries(openenclave_mcounter_host 
	PUBLIC openenclave::oehost
  	PUBLIC mcounter-format
  	PUBLIC zetastub
  	PRIVATE mcounter-verifier)
