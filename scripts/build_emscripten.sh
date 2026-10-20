#!/usr/bin/env bash
# Build checkmate as WebAssembly into html/. Usage (emsdk_env.sh sourced): scripts/build_emscripten.sh Z3_SOURCE_TREE
set -euo pipefail

Z3=$(realpath "$1")
# Single-threaded so the page needs no SharedArrayBuffer (and hence no COOP/COEP headers).
if [ ! -f "$Z3/build-wasm/libz3.a" ]; then
    emcmake cmake -S "$Z3" -B "$Z3/build-wasm" -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_LIBZ3_SHARED=OFF \
        -DZ3_SINGLE_THREADED=ON -DZ3_POLLING_TIMER=ON -DZ3_BUILD_EXECUTABLE=OFF \
        -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_ENABLE_EXAMPLE_TARGETS=OFF \
        -DZ3_INCLUDE_GIT_HASH=OFF -DZ3_INCLUDE_GIT_DESCRIBE=OFF \
        "-DCMAKE_CXX_FLAGS=-fwasm-exceptions" "-DCMAKE_C_FLAGS=-fwasm-exceptions"
    emmake make -C "$Z3/build-wasm" -j"$(nproc)" libz3
fi

emcmake cmake -B build-wasm -DCMAKE_BUILD_TYPE=Release -DZ3_WASM_DIR="$Z3"
emmake make -C build-wasm -j"$(nproc)"
cp build-wasm/checkmate.js build-wasm/checkmate.wasm build-wasm/checkmate-convert.js build-wasm/checkmate-convert.wasm html/

mkdir -p html/examples
cp examples/*/*.json html/examples/
(cd html/examples && ls *.json | grep -v '^index.json$' | python3 -c 'import json, sys; print(json.dumps(sys.stdin.read().split()))' > index.json)
