file(GLOB SRC
  "*.cpp")

add_library(mcounter-host
   ${SRC})

target_include_directories(mcounter-host
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
)

target_link_libraries(mcounter-host
  PUBLIC mcounter-format
  PUBLIC zetastub
)
