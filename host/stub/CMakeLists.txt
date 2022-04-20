file(GLOB STUB_SRC
  "src/*.cpp")

add_library(zetastub ${STUB_SRC})

target_include_directories(zetastub
  PUBLIC ${HOST_DIR}/common/
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include/
  PUBLIC ${PROJECT_BINARY_DIR}
  PUBLIC ${PROJECT_BINARY_DIR}/host
)

target_link_libraries(zetastub
  PRIVATE crypto
  PRIVATE fmt::fmt)
