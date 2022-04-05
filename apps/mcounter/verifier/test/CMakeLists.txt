add_executable(test_mcounter
               test_mcounter.c)

target_link_libraries(test_mcounter
                      PRIVATE verifier)
