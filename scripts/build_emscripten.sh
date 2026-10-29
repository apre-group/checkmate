#!/usr/bin/env bash
# Build checkmate as WebAssembly into html/. Usage (emsdk_env.sh sourced):
#   scripts/build_emscripten.sh Z3_SOURCE_TREE [CVC5_SOURCE_TREE]
# With cvc5, the page also decides the practicality of conditional games that Z3 cannot decide, as checkmate does.
set -euo pipefail

Z3=$(realpath "$1")
CVC5=${2:+$(realpath "$2")}
# Single-threaded so the page needs no SharedArrayBuffer (and hence no COOP/COEP headers).
if [ ! -f "$Z3/build-wasm/libz3.a" ]; then
    emcmake cmake -S "$Z3" -B "$Z3/build-wasm" -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_LIBZ3_SHARED=OFF \
        -DZ3_SINGLE_THREADED=ON -DZ3_POLLING_TIMER=ON -DZ3_BUILD_EXECUTABLE=OFF \
        -DZ3_BUILD_TEST_EXECUTABLES=OFF -DZ3_ENABLE_EXAMPLE_TARGETS=OFF \
        -DZ3_INCLUDE_GIT_HASH=OFF -DZ3_INCLUDE_GIT_DESCRIBE=OFF \
        "-DCMAKE_CXX_FLAGS=-fwasm-exceptions" "-DCMAKE_C_FLAGS=-fwasm-exceptions"
    emmake make -C "$Z3/build-wasm" -j"$(nproc)" libz3
fi

# cvc5 runs as a program for each problem (see cvc5Run in html/index.html), set up synchronously in the worker;
# single-threaded, too (CMake finds Emscripten's pthread stubs, so it is built without -pthread)
if [ -n "$CVC5" ] && [ ! -f "$CVC5/build-wasm/bin/cvc5.wasm" ]; then
    (cd "$CVC5" && ./configure.sh stable --static --static-binary --auto-download --wasm=JS --name=build-wasm \
        --wasm-flags='-s MODULARIZE=1 -s EXPORT_NAME=createCvc5 -s INVOKE_RUN=0 -s EXIT_RUNTIME=0 -s EXPORTED_RUNTIME_METHODS=callMain,FS -s ALLOW_MEMORY_GROWTH=1 -s INITIAL_MEMORY=64MB -s MAXIMUM_MEMORY=4GB -s STACK_SIZE=16MB -s WASM_ASYNC_COMPILATION=0 -s FORCE_FILESYSTEM=1 -fexceptions')
    emmake make -C "$CVC5/build-wasm" -j"$(nproc)" cvc5-bin
fi

emcmake cmake -B build-wasm -DCMAKE_BUILD_TYPE=Release -DZ3_WASM_DIR="$Z3"
emmake make -C build-wasm -j"$(nproc)"
cp build-wasm/checkmate.js build-wasm/checkmate.wasm build-wasm/checkmate-convert.js build-wasm/checkmate-convert.wasm html/
if [ -n "$CVC5" ]; then
    cp "$CVC5/build-wasm/bin/cvc5.js" "$CVC5/build-wasm/bin/cvc5.wasm" html/
fi
# the page loads the modules with this id, so browsers do not keep using an older build
echo "{\"id\": \"$(date +%s)\"}" > html/build.json

# examples over 1 MB (routing_game-four-supertree.json is 57 MB) would hang the page while loading
rm -rf html/examples
mkdir -p html/examples
find examples -name '*.json' -size -1024k -exec cp {} html/examples/ \;
(cd html/examples && ls *.json | grep -v '^index.json$' | python3 -c 'import json, sys; print(json.dumps(sys.stdin.read().split()))' > index.json)
