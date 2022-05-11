# Test sources
file(GLOB TEST_SRC
  "*.cpp"
)

add_executable(test_bits
  ${TEST_SRC})

target_link_libraries(test_bits
  PRIVATE mcounter-host
  PRIVATE Catch2::Catch2
)

target_include_directories(test_bits
  PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})

include (CTest)
include (Catch)
catch_discover_tests(test_bits)
