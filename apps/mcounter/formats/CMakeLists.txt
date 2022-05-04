find_program(MAKE_EXE make)

set (SRC_FILES
     ${CMAKE_CURRENT_SOURCE_DIR}/out/App_key.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/App_val.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Get_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/New_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Incr_p.c
     ${CMAKE_CURRENT_SOURCE_DIR}/out/Slot.c
)

add_custom_command(
   OUTPUT ${SRC_FILES}
   WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
   DEPENDS App.rfc
   COMMAND ${MAKE_EXE})

add_library(mcounter-format
  ${SRC_FILES})

target_include_directories(mcounter-format
  PUBLIC ${DIST_DIR}
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/out
  PUBLIC $ENV{EVERPARSE_HOME}/include
  PRIVATE ${PROJECT_SOURCE_DIR}/verifier
)
