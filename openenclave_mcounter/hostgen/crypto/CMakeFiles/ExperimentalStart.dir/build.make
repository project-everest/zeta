# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local/lib/python3.8/dist-packages/cmake/data/bin/cmake

# The command to remove a file.
RM = /usr/local/lib/python3.8/dist-packages/cmake/data/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/ishtiyaque/veritas-formal/openenclave_mcounter

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/ishtiyaque/veritas-formal/openenclave_mcounter

# Utility rule file for ExperimentalStart.

# Include any custom commands dependencies for this target.
include hostgen/crypto/CMakeFiles/ExperimentalStart.dir/compiler_depend.make

# Include the progress variables for this target.
include hostgen/crypto/CMakeFiles/ExperimentalStart.dir/progress.make

hostgen/crypto/CMakeFiles/ExperimentalStart:
	cd /home/ishtiyaque/veritas-formal/openenclave_mcounter/hostgen/crypto && /usr/local/lib/python3.8/dist-packages/cmake/data/bin/ctest -D ExperimentalStart

ExperimentalStart: hostgen/crypto/CMakeFiles/ExperimentalStart
ExperimentalStart: hostgen/crypto/CMakeFiles/ExperimentalStart.dir/build.make
.PHONY : ExperimentalStart

# Rule to build all files generated by this target.
hostgen/crypto/CMakeFiles/ExperimentalStart.dir/build: ExperimentalStart
.PHONY : hostgen/crypto/CMakeFiles/ExperimentalStart.dir/build

hostgen/crypto/CMakeFiles/ExperimentalStart.dir/clean:
	cd /home/ishtiyaque/veritas-formal/openenclave_mcounter/hostgen/crypto && $(CMAKE_COMMAND) -P CMakeFiles/ExperimentalStart.dir/cmake_clean.cmake
.PHONY : hostgen/crypto/CMakeFiles/ExperimentalStart.dir/clean

hostgen/crypto/CMakeFiles/ExperimentalStart.dir/depend:
	cd /home/ishtiyaque/veritas-formal/openenclave_mcounter && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/ishtiyaque/veritas-formal/openenclave_mcounter /home/ishtiyaque/veritas-formal/openenclave_mcounter/hostgen/crypto /home/ishtiyaque/veritas-formal/openenclave_mcounter /home/ishtiyaque/veritas-formal/openenclave_mcounter/hostgen/crypto /home/ishtiyaque/veritas-formal/openenclave_mcounter/hostgen/crypto/CMakeFiles/ExperimentalStart.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : hostgen/crypto/CMakeFiles/ExperimentalStart.dir/depend

