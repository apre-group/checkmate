cmake_minimum_required(VERSION 3.25)
project(checkmate)
# C++17 for the CEFG engine in src/cefg/ (std::variant, std::optional)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)

add_executable(checkmate
	src/json.hpp
	src/input.hpp
	src/input.cpp
	src/options.hpp
	src/options.cpp
	src/property.hpp
	src/property.cpp
	src/utility.hpp
	src/utils.hpp
	src/z3++.hpp
	src/z3++.cpp
	src/checkmate.cpp
	src/compact.hpp
	src/compact.cpp
	src/validate.hpp
	src/validate.cpp
	src/game_type.hpp
	src/game_type.cpp
	# CEFG engine (conditional extensive form games), in namespace cefg
	src/cefg/run.hpp
	src/cefg/run.cpp
	src/cefg/input.hpp
	src/cefg/input.cpp
	src/cefg/options.hpp
	src/cefg/options.cpp
	src/cefg/utility.hpp
	src/cefg/z3++.hpp
	src/cefg/z3++.cpp
	src/cefg/default_mode.hpp
	src/cefg/default_mode.cpp
	src/cefg/subtree_mode.hpp
	src/cefg/subtree_mode.cpp
	src/cefg/property_checks.hpp
	src/cefg/weak_immunity.cpp
	src/cefg/collusion_resilience.cpp
	src/cefg/practicality.cpp
	src/cefg/selectors.hpp
	src/cefg/selectors.cpp
)
target_link_libraries(checkmate z3)

# JSON <-> compact format, without Z3 (small enough for the web page to convert while typing)
add_executable(checkmate-convert
	src/compact.hpp
	src/compact.cpp
	src/validate.hpp
	src/validate.cpp
	src/game_type.hpp
	src/game_type.cpp
	src/convert.cpp
)

# add extra warnings for GCC/Clang
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
	target_compile_options(checkmate PRIVATE -Wall -Wextra -Wpedantic)
	target_compile_options(checkmate-convert PRIVATE -Wall -Wextra -Wpedantic)
endif()

if(EMSCRIPTEN)
	# WebAssembly build for html/, see scripts/build_emscripten.sh
	set(Z3_WASM_DIR "" CACHE PATH "Z3 source tree with a WebAssembly libz3.a in build-wasm/")
	target_include_directories(checkmate PRIVATE ${Z3_WASM_DIR}/src/api ${Z3_WASM_DIR}/build-wasm/src/api)
	target_link_directories(checkmate PRIVATE ${Z3_WASM_DIR}/build-wasm)
	target_compile_options(checkmate PRIVATE -fwasm-exceptions)
	# as in arjun; the page starts main itself (noInitialRun), in a fresh worker per run
	# (the string functions are for passing problems to cvc5 and its answers back, see run_cvc5 in cefg/selectors.cpp)
	target_link_options(checkmate PRIVATE -fwasm-exceptions
		"SHELL:-s ALLOW_MEMORY_GROWTH=1"
		"SHELL:-s STACK_SIZE=10MB"
		"SHELL:-s EXPORTED_RUNTIME_METHODS='[\"callMain\", \"FS\", \"UTF8ToString\", \"stringToNewUTF8\"]'"
		"SHELL:-s FORCE_FILESYSTEM=1")
	target_compile_options(checkmate-convert PRIVATE -fwasm-exceptions)
	target_link_options(checkmate-convert PRIVATE -fwasm-exceptions
		"SHELL:-s ALLOW_MEMORY_GROWTH=1"
		"SHELL:-s EXPORTED_RUNTIME_METHODS='[\"callMain\", \"FS\"]'"
		"SHELL:-s FORCE_FILESYSTEM=1")
endif()

option(SANITIZE "build with AddressSanitizer and UndefinedBehaviorSanitizer" OFF)
if(SANITIZE)
	target_compile_options(checkmate PRIVATE -fsanitize=address,undefined -fno-omit-frame-pointer)
	target_link_options(checkmate PRIVATE -fsanitize=address,undefined)
endif()
