cmake_minimum_required(VERSION 3.1)
include(CheckCXXSymbolExists)

project(checkmate)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# add extra warnings for GCC/Clang
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
	add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find Z3 build automatically in checkmate/z3/build
find_package(
	Z3
	CONFIG
	NO_CMAKE_PATH
	NO_CMAKE_ENVIRONMENT_PATH
	NO_SYSTEM_ENVIRONMENT_PATH
	NO_CMAKE_PACKAGE_REGISTRY
	NO_CMAKE_SYSTEM_PATH
	NO_CMAKE_SYSTEM_PACKAGE_REGISTRY
	PATHS
		${CMAKE_SOURCE_DIR}/z3/build/
)
if(Z3_FOUND)
	message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
	include_directories(${Z3_CXX_INCLUDE_DIRS})
	link_libraries(${Z3_LIBRARIES})
else()
	message(FATAL_ERROR "No Z3 found: compile it first into checkmate/z3/build/")
endif()

add_executable(checkmate
	src/json.hpp
	src/input.hpp
	src/input.cpp
	src/options.hpp
	src/options.cpp
	src/solver.hpp
	src/solver.cpp
	src/utility.hpp
	src/utils.hpp
	src/weak_immunity.hpp
	src/weak_immunity.cpp
	src/z3++.hpp
	src/z3++.cpp
	src/checkmate.cpp
)
