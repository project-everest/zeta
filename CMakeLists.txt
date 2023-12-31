cmake_minimum_required(VERSION 3.20)

project(zeta LANGUAGES CXX C VERSION 0.1)

# export for ccls
set (CMAKE_EXPORT_COMPILE_COMMANDS ON)

# zeta root directory
cmake_path(SET ZETA_HOME NORMALIZE ${PROJECT_SOURCE_DIR})
message (STATUS "ZETA_HOME = ${ZETA_HOME}")

# extracted verifier code
cmake_path (SET DIST_DIR NORMALIZE "${ZETA_HOME}/steel/dist/")
message (STATUS "DIST_DIR = ${DIST_DIR}")

# hacl dir
cmake_path (SET HACL_DIR NORMALIZE "${DIST_DIR}/hacl-star-v0.3.0/")
message (STATUS "HACL_DIR = ${HACL_DIR}")

# root directory of all apps
cmake_path (SET APP_HOME NORMALIZE "${ZETA_HOME}/apps/")
message (STATUS "APP_HOME = ${APP_HOME}")

# app verifier folder
cmake_path (SET APP_VERIFIER NORMALIZE "${APP_HOME}/verifier/")
message (STATUS "APP_VERIFIER = ${APP_VERIFIER}")

# app verifier folder
cmake_path (SET APP_HOST NORMALIZE "${APP_HOME}/host/")
message (STATUS "APP_HOST = ${APP_HOST}")


# we want to make sure EVERPARSE_HOME env variable is defined
if (NOT DEFINED ENV{EVERPARSE_HOME})
  message (FATAL_ERROR "EVERPARSE_HOME not defined")
endif()

# Default to release builds
if (NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif ()

# Write out the build type
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")

# Trace
if (CMAKE_BUILD_TYPE STREQUAL "Release")
   option(TRACE_MODE "Enable logging of trace information to the console" OFF)
   message(STATUS "Trace mode: ${TRACE_MODE}")
else()
   option(TRACE_MODE "Enable logging of trace information to the console" ON)
   message(STATUS "Trace mode: ${TRACE_MODE}")
endif ()

# configure a header file to pass some of the CMake settings
# to the source code
configure_file(zeta_config.h.in zeta_config.h)

set (STORE_SIZE "16" CACHE STRING "Verifier per-thread store size")
message (STATUS "verifier Store Size = ${STORE_SIZE}")

set (THREAD_COUNT "1" CACHE STRING "Verifier thread count")
message (STATUS "verifier Thread count = ${THREAD_COUNT}")

# enable testing
enable_testing()

# Add Catch2 Unit test framework
find_package(Catch2 REQUIRED)

# fmt package for printing
find_package(fmt REQUIRED)

# spdlog package for logging
find_package(spdlog REQUIRED)

add_subdirectory(apps)
