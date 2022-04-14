# project formats dir
cmake_path (SET APP_FORMATS_DIR NORMALIZE "${PROJECT_SOURCE_DIR}/formats")
message (STATUS "mcounter APP_FORMATS_DIR = ${APP_FORMATS_DIR}")

add_subdirectory(verifier)
add_subdirectory(formats)
