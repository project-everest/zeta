# Test sources
file(GLOB TEST_SRC
  "*.cpp"
)

add_executable(test_mcounter
               ${TEST_SRC})

target_link_libraries(test_mcounter
  PRIVATE mcounter-host
  PRIVATE Catch2::Catch2
)

include (CTest)
include (Catch)
catch_discover_tests(test_mcounter)
