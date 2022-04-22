file(GLOB TEST_SRC *.cpp *.c)
add_executable(hosttest
  ${TEST_SRC}
  ${DIST_DIR}/ZetaFormats.c
)

target_include_directories(hosttest
  PRIVATE ${DIST_DIR}
  PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}
  PRIVATE ${DIST_DIR}
)

target_link_libraries(hosttest
  PRIVATE crypto
  PRIVATE Catch2::Catch2
  PRIVATE zetastub)

include(CTest)
include(Catch)
catch_discover_tests(hosttest)
