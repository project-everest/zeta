cmake_minimum_required(VERSION 3.20)

project(zeta_pwdauth LANGUAGES C VERSION 0.1)

# export for ccls
set (CMAKE_EXPORT_COMPILE_COMMANDS ON)

cmake_path(SET ZETA_HOME NORMALIZE "${CMAKE_CURRENT_SOURCE_DIR}/../../")
message (STATUS "ZETA_HOME = ${ZETA_HOME}")

cmake_path (SET DIST_DIR NORMALIZE "${ZETA_HOME}/steel/dist/")
message (STATUS "DIST_DIR = ${DIST_DIR}")

add_subdirectory(verifier)
