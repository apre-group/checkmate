#!/usr/bin/env bash
# Build checkmate as WebAssembly, and the web page, into html/. Usage:
#   scripts/build_emscripten.sh [Z3_SOURCE_TREE [CVC5_SOURCE_TREE]]
# Z3_SOURCE_TREE defaults to ../z3-4.16.0 next to the repository, cloned if missing.
# Unless emcc is on PATH, sources $EMSDK_ENV (default: ../emsdk/emsdk_env.sh next to the repository).
# With cvc5, the page also decides the practicality of conditional games that Z3 cannot decide, as checkmate does.
set -euo pipefail

PARENT=$(dirname "$(realpath "$0")")/../..
if ! command -v emcc >/dev/null; then
    EMSDK_ENV=${EMSDK_ENV:-$PARENT/emsdk/emsdk_env.sh}
    [ -f "$EMSDK_ENV" ] || { echo "emcc not on PATH and $EMSDK_ENV not found; set EMSDK_ENV" >&2; exit 1; }
    set +u  # emsdk_env.sh reads unset variables
    source "$EMSDK_ENV" >/dev/null 2>&1
    set -u
fi

# the page's TypeScript (html/src) into html/js; `npm run watch` rebuilds just that
[ -d node_modules ] || npm ci
npx tsc -p html

Z3_VERSION=4.16.0
Z3=${1:-$PARENT/z3-$Z3_VERSION}
if [ -z "${1:-}" ] && [ ! -d "$Z3" ]; then
    git clone --depth 1 -b "z3-$Z3_VERSION" https://github.com/Z3Prover/z3 "$Z3"
fi
Z3=$(realpath "$Z3")
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
