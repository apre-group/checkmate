#!/usr/bin/env node
// Print a random game from the web page's generator (html/gen_game.js). Usage: scripts/gen_game_js.js SEED
const fs = require('fs');
const path = require('path');
const vm = require('vm');

vm.runInThisContext(fs.readFileSync(path.join(__dirname, '..', 'html', 'gen_game.js'), 'utf8'));
process.stdout.write(JSON.stringify(genGame(parseInt(process.argv[2], 10) || 0), null, 2) + '\n');
