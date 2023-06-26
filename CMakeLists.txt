# minimum 3.1 for CMAKE_CXX_STANDARD_REQUIRED
cmake_minimum_required(VERSION 3.1)
project(checkmate)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED True)

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
	src/z3++.hpp
	src/z3++.cpp
	src/checkmate.cpp
)
target_link_libraries(checkmate z3)

# add extra warnings for GCC/Clang
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
	target_compile_options(checkmate PRIVATE -Wall -Wextra -Wpedantic)
endif()
