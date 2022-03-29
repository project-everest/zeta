cmake_minimum_required(VERSION 3.16)

project(zeta_pwdauth LANGUAGES C VERSION 0.1)

# export for ccls
set (CMAKE_EXPORT_COMPILE_COMMANDS ON)

set (ZETA_HOME "${CMAKE_CURRENT_SOURCE_DIR}/../..")
message (STATUS "ZETA_HOME = ${ZETA_HOME}")

add_subdirectory(verifier)
