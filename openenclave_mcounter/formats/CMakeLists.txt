find_program(MAKE_EXE make)

file(GLOB SRC_FILES "*.c")

add_library(mcounter-format
  ${SRC_FILES})

cmake_path(SET DIST_DIR NORMALIZE "${CMAKE_CURRENT_SOURCE_DIR}/../dist")
cmake_path(SET EVERPARSE_DIR NORMALIZE "${CMAKE_CURRENT_SOURCE_DIR}/../everparse")
cmake_path(SET EVERPARSE_DIR_INCLUDE NORMALIZE "${EVERPARSE_DIR}/include")

target_include_directories(mcounter-format
  PUBLIC ${DIST_DIR}
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
  PUBLIC ${EVERPARSE_DIR}
  PUBLIC ${EVERPARSE_DIR_INCLUDE}
)
