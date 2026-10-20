#!/usr/bin/env node
// Run the WebAssembly build like the native binary, e.g. for scripts/fuzz.py --wasm.
// Usage: scripts/checkmate_wasm.js [--wasm-dir DIR] GAME [checkmate options...]   (DIR defaults to html/)
const fs = require('fs');
const path = require('path');
const vm = require('vm');

let args = process.argv.slice(2);
let dir = path.join(__dirname, '..', 'html');
if (args[0] === '--wasm-dir') {
    dir = args[1];
    args = args.slice(2);
}
const js = path.resolve(dir, 'checkmate.js');

// Files live in the module's in-memory file system: copy the game in, and what checkmate writes back out.
const inputs = args.length && !args[0].startsWith('--') ? [args[0]] : [];
const outputs = [];
const i = args.indexOf('--json-out');
if (i >= 0 && args[i + 1]) outputs.push(args[i + 1]);
if (args.includes('--subtree') && inputs.length) outputs.push(inputs[0] + '.out');

global.Module = {
    noInitialRun: true,
    print: t => process.stdout.write(t + '\n'),
    printErr: t => process.stderr.write(t + '\n'),
    onRuntimeInitialized() {
        const FS = Module.FS;
        for (const p of inputs) {
            FS.mkdirTree(path.dirname(path.resolve(p)));
            FS.writeFile(path.resolve(p), fs.readFileSync(p));
        }
        for (const p of outputs) FS.mkdirTree(path.dirname(path.resolve(p)));
        let status = 0;
        try {
            const files = new Set(inputs.concat(outputs));
            status = Module.callMain(args.map(a => files.has(a) ? path.resolve(a) : a)) || 0;
        } catch (e) {
            if (e && e.name === 'ExitStatus') status = e.status;
            else { process.stderr.write('checkmate_wasm: ' + e + '\n'); status = 1; }
        }
        for (const p of outputs) {
            try { fs.writeFileSync(p, FS.readFile(path.resolve(p))); } catch (e) { /* not written */ }
        }
        process.exitCode = status;
    },
};

// Evaluated in the global scope, as importScripts does in the page's worker, so the script sees Module.
global.require = require;
global.__dirname = path.dirname(js);
global.__filename = js;
vm.runInThisContext(fs.readFileSync(js, 'utf8'), { filename: js });
