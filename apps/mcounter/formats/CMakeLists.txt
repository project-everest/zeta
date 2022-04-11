find_program(MAKE_EXE make)

set (SRC_FILES
     ${CMAKE_CURRENT_SOURCE_DIR}/out/App_key.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/App_val.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Get_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/New_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Incr_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Slot.c
     ${CMAKE_CURRENT_SOURCE_DIR}/krml_bridge.c
)

add_custom_command(
   OUTPUT ${SRC_FILES}
   WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
   DEPENDS App.rfc
   COMMAND ${MAKE_EXE})

add_library(format
  ${SRC_FILES})

target_include_directories(format
  PUBLIC ${DIST_DIR}
  PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/out
  PRIVATE $ENV{EVERPARSE_HOME}/include
  PRIVATE ${PROJECT_SOURCE_DIR}/verifier
)
