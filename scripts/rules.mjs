#!/usr/bin/env node
// Compile a game described by rules (html/src/rules.ts) into the compact format.
// Usage: scripts/rules.mjs GAME.rules [OUTPUT.game]   (prints to stdout without OUTPUT)
import { readFileSync, writeFileSync } from 'node:fs';
import { compileRules, RulesError } from '../html/src/rules.ts';

const [input, output] = process.argv.slice(2);
if (!input) {
    process.stderr.write('usage: scripts/rules.mjs GAME.rules [OUTPUT.game]\n');
    process.exit(2);
}
try {
    const { text } = compileRules(readFileSync(input, 'utf8'));
    if (output) writeFileSync(output, text);
    else process.stdout.write(text);
} catch (e) {
    if (!(e instanceof RulesError)) throw e;
    process.stderr.write(`rules: ${input}: ${e.message}\n`);
    process.exit(1);
}
