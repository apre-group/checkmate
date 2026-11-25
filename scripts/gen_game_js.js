#!/usr/bin/env node
// Print a random game from the web page's generator (html/src/gen_game.ts). Usage: scripts/gen_game_js.js SEED
const path = require('path');
const { pathToFileURL } = require('url');

import(pathToFileURL(path.join(__dirname, '..', 'html', 'src', 'gen_game.ts')).href).then(({ genGame }) => {
    process.stdout.write(JSON.stringify(genGame(parseInt(process.argv[2], 10) || 0), null, 2) + '\n');
});
