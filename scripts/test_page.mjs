#!/usr/bin/env node
// Test the web page in headless Chromium, after scripts/build_emscripten.sh. Usage: scripts/test_page.mjs [SCENARIO...]
// Chromium is found on the PATH (chromium, google-chrome-stable, ...) or taken from $CHROME.
import { spawn, spawnSync } from 'node:child_process';
import { createServer } from 'node:http';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const HTML = path.join(path.dirname(new URL(import.meta.url).pathname), '..', 'html');
for (const f of ['js/main.js', 'checkmate.wasm', 'checkmate-convert.wasm', 'examples/index.json'])
    if (!existsSync(path.join(HTML, f))) {
        console.error(`html/${f} is missing: build the page first (scripts/build_emscripten.sh)`);
        process.exit(2);
    }
const chromeBinary = process.env.CHROME || ['chromium', 'chromium-browser', 'google-chrome-stable', 'google-chrome']
    .find(c => spawnSync('which', [c]).status === 0);
if (!chromeBinary) {
    console.error('no Chromium found: set CHROME to its path');
    process.exit(2);
}

const TYPES = { '.html': 'text/html', '.js': 'text/javascript', '.wasm': 'application/wasm', '.json': 'application/json' };
const server = createServer((req, res) => {
    const file = path.join(HTML, decodeURIComponent(new URL(req.url, 'http://x').pathname));
    if (!file.startsWith(HTML) || !existsSync(file) || !file.includes('.')) { res.writeHead(404); res.end(); return; }
    res.writeHead(200, { 'Content-Type': TYPES[path.extname(file)] || 'text/plain' });
    res.end(readFileSync(file));
});
await new Promise(r => server.listen(0, '127.0.0.1', r));
const url = `http://127.0.0.1:${server.address().port}/index.html`;

const profile = mkdtempSync(path.join(tmpdir(), 'checkmate-page-'));
const chrome = spawn(chromeBinary, ['--headless=new', '--remote-debugging-port=0', `--user-data-dir=${profile}`,
    '--window-size=1300,1000', '--no-first-run', 'about:blank'], { stdio: ['ignore', 'ignore', 'pipe'] });
const wsUrl = await new Promise((resolve, reject) => {
    let err = '';
    chrome.stderr.on('data', d => { err += d; const m = err.match(/DevTools listening on (ws:\S+)/); if (m) resolve(m[1]); });
    chrome.on('exit', () => reject(new Error('Chromium exited: ' + err)));
});
const sleep = ms => new Promise(r => setTimeout(r, ms));

// one page over the DevTools protocol; `problems` collects exceptions and console errors
const ws = new WebSocket(wsUrl);
await new Promise(r => ws.addEventListener('open', r));
let next = 1, session = null;
const pending = new Map(), problems = [];
// 404s the page expects: no favicon, and cvc5 only if it was built
const EXPECTED_404 = /favicon\.ico|cvc5\.wasm/;
ws.addEventListener('message', e => {
    const m = JSON.parse(e.data);
    if (m.id && pending.has(m.id)) { pending.get(m.id)(m); pending.delete(m.id); return; }
    const p = m.params;
    if (m.method === 'Runtime.exceptionThrown') problems.push('exception: ' + (p.exceptionDetails.exception?.description || p.exceptionDetails.text));
    if (m.method === 'Runtime.consoleAPICalled' && ['error', 'warning'].includes(p.type))
        problems.push(`console.${p.type}: ` + p.args.map(a => a.value ?? a.description).join(' '));
    if (m.method === 'Log.entryAdded' && p.entry.level === 'error' && !EXPECTED_404.test(p.entry.url || ''))
        problems.push('log: ' + p.entry.text + ' ' + (p.entry.url || ''));
});
const send = (method, params = {}) => new Promise((resolve, reject) => {
    const id = next++;
    pending.set(id, m => m.error ? reject(new Error(method + ': ' + m.error.message)) : resolve(m.result));
    ws.send(JSON.stringify({ id, method, params, ...(session ? { sessionId: session } : {}) }));
});
const { targetId } = await send('Target.createTarget', { url: 'about:blank' });
session = (await send('Target.attachToTarget', { targetId, flatten: true })).sessionId;
await send('Runtime.enable'); await send('Log.enable'); await send('Page.enable');

const evaluate = async expr => {
    const r = await send('Runtime.evaluate', { expression: expr, awaitPromise: true, returnByValue: true });
    if (r.exceptionDetails) throw new Error('in the page: ' + (r.exceptionDetails.exception?.description || r.exceptionDetails.text));
    return r.result.value;
};
const waitFor = async (expr, what, ms = 30000) => {
    for (let t = 0; t < ms; t += 50) {
        try { if (await evaluate(expr)) return; } catch {}
        await sleep(50);
    }
    throw new Error('timed out waiting for ' + (what || expr));
};
const check = (ok, message) => { if (!ok) throw new Error(message); };
const equal = (actual, expected, what) => check(actual === expected, `${what}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);

const text = id => evaluate(`document.getElementById(${JSON.stringify(id)}).textContent`);
const players = () => evaluate(`[...document.querySelectorAll('#tree .t-player')].map(t => t.textContent)`);
const status = () => text('status');
async function load() {
    await send('Page.navigate', { url });
    await waitFor(`document.getElementById('status').textContent === 'Ready' && document.querySelectorAll('#tree .t-node').length > 0`, 'the page to load');
}
async function pick(name) {
    await evaluate(`{ const s = document.getElementById('example'); s.value = ${JSON.stringify(name)}; s.dispatchEvent(new Event('change')); }`);
    await waitFor(`document.getElementById('game').value.length > 0 && !document.getElementById('game').dataset.old`, name);
}
// put `content` in the editor, as typing would, and wait for the tree or the error below the editor to change
async function type(content) {
    const now = `document.getElementById('tree').innerHTML + '\\n' + document.getElementById('parse-error').textContent`;
    const before = await evaluate(now);
    await evaluate(`{ const g = document.getElementById('game'); g.value = ${JSON.stringify(content)}; g.dispatchEvent(new Event('input')); }`);
    await waitFor(`${now} !== ${JSON.stringify(before)}`, 'the tree or the error to change');
}
async function run() {
    await evaluate(`document.getElementById('run').click()`);
    await waitFor(`/^(Done|Failed)/.test(document.getElementById('status').textContent)`, 'the run to finish', 120000);
    const s = await status();
    check(s.startsWith('Done'), 'run: ' + s + '\n' + await text('output'));
}
const verdicts = () => evaluate(`[...document.querySelectorAll('#results tr')].slice(1).map(tr => [...tr.cells].map(c => c.textContent).join(' ')).join(' | ')`);
async function selectExample(name) {
    // wait until the game in the editor is the example's (an example changes the editor once loaded)
    const before = await evaluate(`document.getElementById('game').value`);
    await evaluate(`{ const s = document.getElementById('example'); s.value = ${JSON.stringify(name)}; s.dispatchEvent(new Event('change')); }`);
    await waitFor(`document.getElementById('game').value !== ${JSON.stringify(before)} || ${JSON.stringify(name)} === 'loan.rules'`, name);
    await waitFor(`document.querySelectorAll('#tree .t-node').length > 0 || document.getElementById('parse-error').textContent`, name);
}

const SCENARIOS = {
    async 'the default example'() {
        equal(await evaluate(`document.getElementById('example').value`), 'loan.rules', 'example');
        check(!(await evaluate(`document.getElementById('generated').hidden`)), 'the generated tree is hidden');
        equal(await text('generated-count'), '3 ways to play', 'generated');
        check((await text('glossary')).includes('Alice has money to lend'), 'glossary: ' + await text('glossary'));
        equal((await players()).sort().join(), 'Alice,Bob', 'players');
        equal(await evaluate(`[...document.querySelectorAll('#tree .t-described')].map(t => t.textContent).sort().join()`), 'keep,refuse,repay', 'described actions');
        equal(await evaluate(`document.querySelectorAll('#tree .t-leaf').length`), 3, 'leaves');
        await run();
        equal(await verdicts(), 'lend → repay NO NO NO NO', 'verdicts');
        await evaluate(`document.querySelectorAll('.verdict')[3].click()`);
        check((await text('explain')).includes('Bob is better off playing keep after lend'), await text('explain'));
        await selectExample('loan_with_deposit.rules');
        await run();
        equal(await verdicts(), 'lend → repay YES YES YES YES', 'verdicts with a deposit');
    },

    async 'running it, and the results in words'() {
        await selectExample('market_entry.rules');
        await run();
        equal(await verdicts(), 'stay_out YES YES YES NO | enter → share NO NO YES YES | enter → fight NO NO NO NO', 'verdicts');
        const n = await evaluate(`document.querySelectorAll('.verdict').length`);
        for (let i = 0; i < n; i++) {
            await evaluate(`document.querySelectorAll('.verdict')[${i}].click()`);
            const words = await text('explain'), holds = await evaluate(`document.querySelectorAll('.verdict')[${i}].textContent === 'YES'`);
            check(/^(Weak immunity|Weaker immunity|Collusion resilience|Practicality):/.test(words), `verdict ${i}: ${words}`);
            check(words.includes(holds ? 'Yes, for' : 'No, not for'), `verdict ${i}: ${words}`);
            const red = await evaluate(`document.querySelectorAll('#tree .t-edge.ce').length`);
            const green = await evaluate(`document.querySelectorAll('#tree .t-edge.strategy').length`);
            check(holds ? green > 0 && red === 0 : red > 0, `verdict ${i}: ${green} strategy and ${red} counterexample edges`);
        }
        await evaluate(`document.querySelectorAll('.verdict')[3].click()`);
        check((await text('explain')).includes('Newcomer is better off playing enter at the start'), await text('explain'));
    },

    async 'every example loads'() {
        const names = await evaluate(`[...document.querySelectorAll('#example option')].map(o => o.value)`);
        check(names.length > 10, 'examples: ' + names);
        for (const name of names) {
            await selectExample(name);
            equal(await text('parse-error'), '', name);
            check(await evaluate(`document.querySelectorAll('#tree .t-node').length > 0`), name + ': no tree');
        }
    },

    async 'the rules examples run'() {
        for (const [name, expected] of [['closing_channel.rules', 'close_alone YES YES YES NO | propose_close → sign NO NO YES YES'],
                                        ['centipede.rules', 'pass → pass → pass → pass → pass → pass YES YES NO NO']]) {
            await selectExample(name);
            await run();
            equal(await verdicts(), expected, name);
        }
        await evaluate(`document.querySelectorAll('.verdict')[3].click()`);
        check((await text('explain')).includes('Bob is better off playing take'), await text('explain'));
    },

    async 'errors in rules point at their line'() {
        await selectExample('centipede.rules');
        const rules = await evaluate(`document.getElementById('game').value`);
        await type(rules.replace('if round < 6', 'if rond < 6'));
        equal(await text('parse-error'), 'line 16: unknown name rond', 'error');
        equal(await evaluate(`document.querySelector('.h-error').textContent`), '  if rond < 6', 'marked line');
        // an error that only the converter finds, in the tree the rules give
        await type(rules.replace('initial: coin > 0', 'initial: coin >> 0'));
        check((await text('parse-error')).startsWith('line 6: '), await text('parse-error'));
        equal(await evaluate(`document.querySelector('.h-error').textContent`), 'initial: coin >> 0', 'marked line');
        await type(rules);
        equal(await text('parse-error'), '', 'fixed');
    },

    async 'errors in a game tree point at their line'() {
        await selectExample('market_entry.game');
        const game = await evaluate(`document.getElementById('game').value`);
        await type(game.replace('honest share -> Newcomer: profit,', 'honest share -> Nobody: profit,'));
        check(/^line \d+: unknown player Nobody/.test(await text('parse-error')), await text('parse-error'));
        check((await evaluate(`document.querySelector('.h-error').textContent`)).includes('Nobody'), 'marked line');
        check(await evaluate(`document.getElementById('generated').hidden`), 'a tree has no generated tree');
    },

    async 'pasted JSON becomes the compact format'() {
        const json = readFileSync(path.join(HTML, 'examples', 'market_entry_game.json'), 'utf8');
        await type(json);
        await waitFor(`document.getElementById('game').value.startsWith('players: N, E')`, 'the compact format');
        equal((await players()).sort().join(), 'E,N', 'players');
    },

    async 'a random game'() {
        await evaluate(`document.getElementById('seed').value = '42'; document.getElementById('random').click()`);
        await waitFor(`document.getElementById('status').textContent === 'Random game with seed 42'`);
        await waitFor(`!document.getElementById('game').value.includes('Newcomer') && document.getElementById('game').value.startsWith('players')`);
        await run();
        check((await verdicts()).length > 0, 'no verdicts');
    },

    async 'a conditional game'() {
        await type(`players: A, B
unknown_constants: y
initial: y = 0 | y = 1

A
  hon -> A: 2, B: 0
  honest dev -> A
    safe -> A: 1, B: 0
    honest risk -> ? reveals y
      if low: y = 0 -> B
        honest l -> A: 1, B: 1
        r -> A: 0, B: 2
      if y = 1 -> A: 3, B: 0
`);
        equal(await evaluate(`document.querySelectorAll('#tree .t-cond-node').length`), 1, 'condition nodes');
        equal(await evaluate(`document.querySelectorAll('#tree .t-band').length`), 5, 'honest edges');
        await run();
        equal(await verdicts(), 'dev → risk → {if (y = 0.0) → l; if (y = 1.0)} YES YES NO NO', 'verdicts');
    },

    async 'long player names are shortened to fit'() {
        await type(`players: Captain_Anne_Bonny, Bosun_Bartholomew_Roberts
state: round = 0

honest move left by Captain_Anne_Bonny, Bosun_Bartholomew_Roberts
  if round < 4
  set round = round + 1
  next other
move middle by Captain_Anne_Bonny, Bosun_Bartholomew_Roberts
  if round < 4
  set round = round + 1
  next other
move right by Captain_Anne_Bonny, Bosun_Bartholomew_Roberts
  if round < 4
  set round = round + 1
  next other
honest move stop by Captain_Anne_Bonny, Bosun_Bartholomew_Roberts
  if round = 4
  end
`);
        for (const button of [null, 'unfold-all']) {
            if (button) await evaluate(`document.getElementById('${button}').click()`);
            // shortened to what fits, with … if there is room for it
            const names = await players(), full = ['Captain_Anne_Bonny', 'Bosun_Bartholomew_Roberts'];
            check(names.every(n => full.some(f => n !== f && f.startsWith(n.replace(/…$/, '')))), 'not shortened: ' + names.slice(0, 5));
            // no two players on one level overlap
            const overlap = await evaluate(`{
                const rs = [...document.querySelectorAll('#tree rect.t-node')].map(r => r.getBBox());
                rs.some((a, i) => rs.some((b, j) => i < j && a.y === b.y && a.x < b.x + b.width && b.x < a.x + a.width));
            }`);
            check(!overlap, `players overlap (${button || 'folded'})`);
        }
        const unfolded = await evaluate(`document.querySelectorAll('#tree .t-node').length`);
        await evaluate(`document.getElementById('fold-default').click()`);
        check(await evaluate(`document.querySelectorAll('#tree .t-node').length`) < unfolded, 'folding does not fold');
        check((await evaluate(`document.querySelector('#tree [data-tip]') !== null`)), 'no tooltips');
    },

    async 'the theme switches'() {
        const before = await evaluate(`getComputedStyle(document.body).backgroundColor`);
        await evaluate(`document.getElementById('theme').click()`);
        check(['light', 'dark'].includes(await evaluate(`document.documentElement.dataset.theme`)), 'no theme set');
        check(await evaluate(`getComputedStyle(document.body).backgroundColor`) !== before, 'the colours did not change');
    },
};

const chosen = process.argv.slice(2);
let failed = 0;
for (const [name, scenario] of Object.entries(SCENARIOS)) {
    if (chosen.length && !chosen.some(c => name.includes(c))) continue;
    problems.length = 0;
    const started = performance.now();
    try {
        await load();
        await scenario();
        check(!problems.length, 'in the page:\n  ' + problems.join('\n  '));
        console.log(`ok: ${name} (${((performance.now() - started) / 1000).toFixed(1)} s)`);
    } catch (e) {
        failed++;
        console.log(`FAIL: ${name}: ${e.message}`);
    }
}
// closing the browser (rather than killing it) lets its other processes finish writing to the profile
const exited = new Promise(r => chrome.on('exit', r));
session = null;
await Promise.race([send('Browser.close').catch(() => {}), sleep(5000)]);
await Promise.race([exited, sleep(5000).then(() => chrome.kill())]);
ws.close();
server.close();
rmSync(profile, { recursive: true, force: true, maxRetries: 10, retryDelay: 100 });
process.exit(failed ? 1 : 0);
