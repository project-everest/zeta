find_program(MAKE_EXE make)

set (SRC_FILES ${CMAKE_CURRENT_SOURCE_DIR}/out/App_key.c ${CMAKE_CURRENT_SOURCE_DIR}/out/App_val.c)

add_custom_command(
  OUTPUT ${SRC_FILES}
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  DEPENDS App.rfc
  COMMAND ${MAKE_EXE})

add_library(format
  ${SRC_FILES})

target_include_directories(format
  PRIVATE $ENV{EVERPARSE_HOME}/include/
  PRIVATE $ENV{EVERPARSE_HOME}/kremlib/dist/generic/
  )
