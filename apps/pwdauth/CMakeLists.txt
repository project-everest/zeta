cmake_minimum_required(VERSION 3.20)

project(zeta_pwdauth LANGUAGES C VERSION 0.1)

# export for ccls
set (CMAKE_EXPORT_COMPILE_COMMANDS ON)

# zeta root directory
cmake_path(SET ZETA_HOME NORMALIZE "${CMAKE_CURRENT_SOURCE_DIR}/../../")
message (STATUS "ZETA_HOME = ${ZETA_HOME}")

# extracted verifier code
cmake_path (SET DIST_DIR NORMALIZE "${ZETA_HOME}/steel/dist/")
message (STATUS "DIST_DIR = ${DIST_DIR}")

# root directory of all apps
cmake_path (SET APP_HOME NORMALIZE "${CMAKE_CURRENT_SOURCE_DIR}/../")
message (STATUS "APP_HOME = ${APP_HOME}")

# we want to make sure EVERPARSE_HOME env variable is defined
if (NOT DEFINED ENV{EVERPARSE_HOME})
  message (FATAL_ERROR "EVERPARSE_HOME not defined")
endif()

add_subdirectory(verifier)
