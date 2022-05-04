add_executable(test_mcounter
               test_mcounter.cpp)

target_link_libraries(test_mcounter
                      PRIVATE mcounter-host
                      PRIVATE mcounter-verifier
                      PRIVATE mcounter-format
                      )
