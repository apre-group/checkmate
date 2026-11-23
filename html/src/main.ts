import type { Condition, Declarations, Game, HistoryElement, Result, Step, TreeNode } from './game.ts';
import { genGame } from './gen_game.ts';
import { highlightCompact, highlightRules } from './highlight.ts';
import { compileRules, looksLikeRules, RulesError, type Compiled } from './rules.ts';
import { explain, type Item } from './explain.ts';
import { NAMES, caseText, escapeHtml, historyText } from './text.ts';

// the page's elements exist, so this is never null
const $ = <T extends Element = HTMLElement>(id: string) => document.getElementById(id) as Element as T;
// the build id makes browsers fetch the modules again after a rebuild, and cache them otherwise
const version: Promise<string> = fetch('build.json', { cache: 'no-store' }).then(r => r.json())
    .then((b: { id: string }) => '?v=' + b.id).catch(() => '');

let game: Game | null = null, results: Result[] | null = null, selection: Item | null = null, worker: Worker | null = null;

// ---- theme ----------------------------------------------------------------

// Without a saved choice the page follows the system; the button switches to the other theme and remembers it.
$('theme').addEventListener('click', () => {
    const current = document.documentElement.dataset.theme ||
        (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
    const next = current === 'dark' ? 'light' : 'dark';
    document.documentElement.dataset.theme = next;
    try { localStorage.setItem('theme', next); } catch (e) {}
});

// ---- examples -------------------------------------------------------------

fetch('examples/index.json').then(r => r.json()).then((names: string[]) => {
    const group = (label: string, ns: string[]) =>
        ns.length ? `<optgroup label="${label}">` + ns.map(n => `<option>${n}</option>`).join('') + '</optgroup>' : '';
    $<HTMLSelectElement>('example').innerHTML = group('Rules', names.filter(n => n.endsWith('.rules'))) +
        group('Game trees', names.filter(n => n.endsWith('.game'))) +
        group('From the papers', names.filter(n => n.endsWith('.json')));
    const start = ['market_entry.rules', 'market_entry.game', 'market_entry_game.json'].find(n => names.includes(n)) || names[0];
    $<HTMLSelectElement>('example').value = start;
    loadExample(start);
}).catch(() => { $<HTMLSelectElement>('example').innerHTML = '<option value="">(no examples found)</option>'; });

$<HTMLSelectElement>('example').addEventListener('change', () => loadExample($<HTMLSelectElement>('example').value));

$('random').addEventListener('click', () => {
    const typed = parseInt($<HTMLInputElement>('seed').value, 10);
    const seed = Number.isNaN(typed) ? Math.floor(Math.random() * 1e9) : typed;
    $<HTMLInputElement>('seed').value = '';
    $<HTMLInputElement>('seed').placeholder = String(seed);
    $<HTMLSelectElement>('example').value = '';
    showGame(JSON.stringify(genGame(seed), null, 2));
    $('status').textContent = 'Random game with seed ' + seed;
});

// ---- converting between JSON and the compact format ------------------------

// One long-lived worker with the small converter module: main has no global state, so it can run again and again.
const converter = (() => {
    const source = `
        var Module = {
            noInitialRun: true,
            // not self.out/self.err: the Emscripten script defines globals with those names
            print: t => self.convertOut.push(t),
            printErr: t => self.convertErr.push(t),
            locateFile: p => p.endsWith('.wasm') ? self.base + 'checkmate-convert.wasm' + self.v : self.base + p,
            onRuntimeInitialized: () => postMessage({ type: 'ready' })
        };
        onmessage = e => {
            if (e.data.type === 'init') {
                self.base = e.data.base;
                self.v = e.data.v;
                importScripts(e.data.base + 'checkmate-convert.js' + self.v);
                return;
            }
            self.convertOut = []; self.convertErr = [];
            let result = null;
            try {
                Module.FS.writeFile('/in', e.data.text);
                if (Module.callMain(['/in', '/out']) === 0) result = Module.FS.readFile('/out', { encoding: 'utf8' });
            } catch (err) {
                if (!(err && err.name === 'ExitStatus')) self.convertErr.push(err && err.message ? err.message : String(err));
            }
            postMessage({ type: 'result', id: e.data.id, result, error: self.convertErr.join('\\n') });
        };`;
    const w = new Worker(URL.createObjectURL(new Blob([source], { type: 'application/javascript' })));
    const pending = new Map<number, { resolve: (text: string) => void, reject: (err: Error) => void }>();
    let next = 0, readyResolve: () => void;
    const ready = new Promise<void>(r => { readyResolve = r; });
    w.onmessage = e => {
        if (e.data.type === 'ready') return readyResolve();
        const p = pending.get(e.data.id)!;
        pending.delete(e.data.id);
        if (e.data.result !== null) p.resolve(e.data.result);
        else p.reject(new Error(e.data.error.replace(/^checkmate-convert: /, '') || 'conversion failed'));
    };
    version.then(v => w.postMessage({ type: 'init', base: new URL('.', location.href).href, v }));
    // JSON becomes compact text, compact text becomes JSON
    return (text: string) => ready.then(() => new Promise<string>((resolve, reject) => {
        const id = next++;
        pending.set(id, { resolve, reject });
        w.postMessage({ type: 'convert', id, text });
    }));
})();

const looksLikeJson = (text: string) => text.trimStart().startsWith('{');

async function showGame(jsonText: string) {
    folded = null;  // a new game gets the default folding
    try {
        $<HTMLTextAreaElement>('game').value = await converter(jsonText);
    } catch (e) {
        // a game without a compact form (e.g. names with spaces) stays JSON; gameChanged would bring it back here
        $<HTMLTextAreaElement>('game').value = jsonText;
        results = null; selection = null;
        $('results').textContent = 'Run CheckMate to see results.';
        $('cases').innerHTML = '';
        $('explain').innerHTML = '';
        game = JSON.parse(jsonText);
        $('parse-error').textContent = '';
        errorLine = 0;
        highlight();
        drawTree();
        return;
    }
    gameChanged();
}

function loadExample(name: string) {
    if (!name) return;
    fetch('examples/' + name).then(r => r.text()).then(text => {
        if (looksLikeJson(text)) return showGame(text);
        $<HTMLTextAreaElement>('game').value = text;
        $<HTMLTextAreaElement>('game').scrollTop = 0;
        folded = null;
        return gameChanged();
    });
}

// the game tree that the rules in the editor give, if the editor has rules
let compiled: Compiled | null = null;

let editTimer: ReturnType<typeof setTimeout> | undefined, errorLine = 0;
function highlight() {
    const text = $<HTMLTextAreaElement>('game').value;
    $('highlight').innerHTML = (looksLikeRules(text) ? highlightRules : highlightCompact)(text, errorLine);
    syncScroll();
}
function showGenerated() {
    $('generated').hidden = !compiled;
    if (!compiled) return;
    $('generated-count').textContent = `${compiled.leaves} way${compiled.leaves === 1 ? '' : 's'} to play`;
    $('generated-text').innerHTML = highlightCompact(compiled.text, 0);
}
function syncScroll() {
    $('highlight').scrollTop = $<HTMLTextAreaElement>('game').scrollTop;
    $('highlight').scrollLeft = $<HTMLTextAreaElement>('game').scrollLeft;
}
$<HTMLTextAreaElement>('game').addEventListener('scroll', syncScroll);
$<HTMLTextAreaElement>('game').addEventListener('input', () => {
    highlight();
    clearTimeout(editTimer);
    editTimer = setTimeout(gameChanged, 250);
});

// Parse the editor's text into `game` (for the tree); pasted JSON is shown in the compact format.
async function gameChanged() {
    results = null; selection = null;
    $('results').textContent = 'Run CheckMate to see results.';
    $('cases').innerHTML = '';
    $('explain').innerHTML = '';
    const text = $<HTMLTextAreaElement>('game').value;
    highlight();
    compiled = null;
    if (looksLikeJson(text)) {
        showGenerated();
        try { JSON.parse(text); } catch (e) { $('parse-error').textContent = 'Invalid JSON: ' + (e as Error).message; return; }
        return showGame(text);
    }
    if (looksLikeRules(text)) {
        try {
            compiled = compileRules(text);
        } catch (e) {
            if (!(e instanceof RulesError)) throw e;
            $('parse-error').textContent = e.message;
            errorLine = e.line;
            highlight();
            showGenerated();
            return;  // keep showing the last good tree
        }
    }
    showGenerated();
    const generated = compiled;
    try {
        const jsonText = await converter(generated ? generated.text : text);
        if ($<HTMLTextAreaElement>('game').value !== text) return;  // edited again meanwhile
        game = JSON.parse(jsonText);
        $('parse-error').textContent = '';
        errorLine = 0;
        highlight();
    } catch (e) {
        if ($<HTMLTextAreaElement>('game').value !== text) return;
        let message = (e as Error).message;
        const m = message.match(/^line (\d+):/);
        errorLine = m ? +m[1] : 0;
        // an error in the generated tree, at the line of the rules that gave it
        if (generated && m) {
            errorLine = generated.lines[errorLine] || 0;
            message = `line ${errorLine}: ` + message.slice(m[0].length).trim();
        }
        $('parse-error').textContent = message;
        highlight();
        return;  // keep showing the last good tree
    }
    drawTree();
}

// ---- running checkmate in a worker -----------------------------------------

// A fresh worker per run: checkmate keeps global state, and cancelling means terminating the worker.
function workerSource() {
    return `
        // cvc5 on a SyGuS problem, for run_cvc5 in src/cefg/selectors.cpp: a fresh instance for every problem, as
        // cvc5 runs as a program for each; null if the page did not load cvc5. Checkmate waits for the answer, so
        // the instance is set up synchronously, from the bytes of cvc5.wasm (an instantiateWasm hook would
        // finish the set-up only after an await)
        self.cvc5Run = (problem, timeout) => {
            if (!self.cvc5) return null;
            const out = [], cvc5 = { print: t => out.push(t), printErr: t => out.push(t), wasmBinary: self.cvc5 };
            createCvc5(cvc5);
            cvc5.FS.writeFile('/problem.sy', problem);
            // --tlimit needs a timer signal, which cannot interrupt a computation in the browser
            try { cvc5.callMain(['--lang', 'sygus2', '--tlimit-per=' + timeout, '/problem.sy']); } catch (err) {
                if (!(err && err.name === 'ExitStatus')) out.push('error: ' + err);
            }
            return out.join('\\n');
        };
        var Module = {
            noInitialRun: true,
            print: t => postMessage({ type: 'output', content: t }),
            printErr: t => postMessage({ type: 'output', content: t }),
            locateFile: p => p.endsWith('.wasm') ? self.base + 'checkmate.wasm' + self.v : self.base + p,
            onRuntimeInitialized: () => postMessage({ type: 'ready' })
        };
        onmessage = e => {
            if (e.data.type === 'init') {
                self.base = e.data.base;
                self.v = e.data.v;
                self.cvc5 = e.data.cvc5 && new Uint8Array(e.data.cvc5);
                if (self.cvc5) importScripts(e.data.base + 'cvc5.js' + self.v);
                importScripts(e.data.base + 'checkmate.js' + self.v);
            } else if (e.data.type === 'run') {
                let result = null;
                try {
                    Module.FS.writeFile('/game.txt', e.data.game);
                    Module.callMain(['/game.txt'].concat(e.data.args).concat(['--json-out', '/result.json']));
                } catch (err) {
                    if (!(err && err.name === 'ExitStatus')) postMessage({ type: 'output', content: 'Error: ' + err });
                }
                try { result = Module.FS.readFile('/result.json', { encoding: 'utf8' }); } catch (err) {}
                postMessage({ type: 'done', result });
            }
        };`;
}

// cvc5 compiled to WebAssembly (by scripts/build_emscripten.sh), for the practicality of conditional games when
// Z3 cannot decide it: loaded once, when a run first needs it, and handed to the worker of every run that does;
// null if it is not on the page
let cvc5Loaded: Promise<ArrayBuffer | null> | null = null;
function cvc5Wasm() {
    if (!cvc5Loaded)
        cvc5Loaded = version.then(v => fetch('cvc5.wasm' + v)).then(r => r.ok ? r.arrayBuffer() : Promise.reject())
            .catch(() => null);
    return cvc5Loaded;
}

// is the game conditional (as detect_game_type in src/game_type.cpp decides), so that its practicality may need cvc5?
function isCefg(g: Game) {
    const unknowns = ([g.constants, g.infinitesimals]).some(d => d && !Array.isArray(d) && (d.unknown || []).length);
    const conditional = (n: TreeNode): boolean => isCondition(n) || Array.isArray(n.subtree) || (n.children || []).some(c => conditional(c.child));
    const honest = (g.honest_utilities || []).some(u => (u.utility || []).some(e => e && 'condition' in e));
    return unknowns || conditional(g.tree) || honest;
}

function parseArgs(str: string) {
    return (str.match(/"[^"]*"|\S+/g) || []).map(a => a.replace(/^"|"$/g, ''));
}

$<HTMLButtonElement>('run').addEventListener('click', () => {
    if (!game || $('parse-error').textContent) { $('status').textContent = 'Fix the game first.'; return; }
    const props = [...document.querySelectorAll<HTMLInputElement>('.prop:checked')].map(c => c.value);
    const args = (props.length === 4 ? [] : props)
        .concat([...document.querySelectorAll<HTMLInputElement>('.opt:checked')].map(c => c.value))
        .concat(parseArgs($<HTMLInputElement>('extra').value));
    $('output').textContent = '';
    $('status').textContent = 'Running…';
    $<HTMLButtonElement>('run').disabled = true;
    $<HTMLButtonElement>('cancel').disabled = false;
    const started = performance.now();
    const needsCvc5 = (props.length === 4 || props.includes('--practicality')) && isCefg(game);
    const url = URL.createObjectURL(new Blob([workerSource()], { type: 'application/javascript' }));
    const w = new Worker(url);
    worker = w;
    const out: string[] = [];
    w.onmessage = e => {
        const d = e.data;
        if (d.type === 'output') {
            out.push(d.content);
            if (out.length % 50 === 0) $('output').textContent = out.join('\n');
        } else if (d.type === 'ready') {
            w.postMessage({ type: 'run', game: compiled ? compiled.text : $<HTMLTextAreaElement>('game').value, args });
        } else if (d.type === 'done') {
            $('output').textContent = out.join('\n');
            finish(d.result ? 'Done in ' + ((performance.now() - started) / 1000).toFixed(2) + ' s'
                            : 'Failed, see the output below');
            URL.revokeObjectURL(url);
            showResults(d.result ? JSON.parse(d.result).results : null);
        }
    };
    if (needsCvc5 && !cvc5Loaded) $('status').textContent = 'Loading cvc5…';
    Promise.all([version, needsCvc5 ? cvc5Wasm() : null]).then(([v, cvc5]) => {
        if (worker !== w) return;  // cancelled meanwhile
        $('status').textContent = 'Running…';
        w.postMessage({ type: 'init', base: new URL('.', location.href).href, v, cvc5 });
    });
});

$<HTMLButtonElement>('cancel').addEventListener('click', () => { finish('Cancelled'); });

function finish(status: string) {
    if (worker) worker.terminate();
    worker = null;
    $('status').textContent = status;
    $<HTMLButtonElement>('run').disabled = false;
    $<HTMLButtonElement>('cancel').disabled = true;
}

// Check that the module loads at all before enabling Run.
fetch('checkmate.wasm', { method: 'HEAD' }).then(r => {
    if (!r.ok) throw new Error();
    $('status').textContent = 'Ready';
    $<HTMLButtonElement>('run').disabled = false;
}).catch(() => { $('status').textContent = 'checkmate.wasm not found: build it with scripts/build_emscripten.sh'; });

// ---- results ----------------------------------------------------------------

function showResults(rs: Result[] | null) {
    results = rs; selection = null;
    $('cases').innerHTML = '';
    $('explain').innerHTML = '';
    if (!rs) { $('results').textContent = 'No results (see the output below).'; drawTree(); return; }
    // a row per honest history; CEFGs also have runs without one, collusion resilience once per honest utility
    const rowKey = (r: Result) => JSON.stringify([r.history, r.honest_utility]);
    const rows = [...new Map(rs.map(r => [rowKey(r), r])).values()];
    const props = Object.keys(NAMES).filter(p => rs.some(r => r.property === p));
    let html = '<table><tr><th>honest history</th>' + props.map(p => `<th>${NAMES[p]}</th>`).join('') + '</tr>';
    for (const row of rows) {
        const label = row.history ? historyText(row.history) || '(empty)'
            : row.honest_utility !== undefined ? `(honest utility ${row.honest_utility + 1})` : '(no honest history)';
        html += `<tr><td>${escapeHtml(label)}</td>`;
        for (const p of props) {
            const i = rs.findIndex(r => r.property === p && rowKey(r) === rowKey(row));
            if (i < 0) { html += '<td></td>'; continue; }
            // CEFGs: holds is null if practicality could not be decided
            const [cls, text] = rs[i].holds === null ? ['undecided', '?'] : rs[i].holds ? ['yes', 'YES'] : ['no', 'NO'];
            const title = rs[i].undecided ? ` title="${escapeHtml(rs[i].undecided)}"` : '';
            html += `<td class="verdict ${cls}" data-i="${i}"${title}>${text}</td>`;
        }
        html += '</tr>';
    }
    $('results').innerHTML = html + '</table>';
    document.querySelectorAll<HTMLElement>('.verdict').forEach(td => td.addEventListener('click', () => selectResult(+td.dataset.i!, td)));
    const first = document.querySelector<HTMLElement>('.verdict');
    if (first) selectResult(+first.dataset.i!, first);
}

function selectResult(i: number, td: HTMLElement) {
    document.querySelectorAll('.verdict').forEach(x => x.classList.remove('selected'));
    td.classList.add('selected');
    const r = results![i];
    const items: Item[] = [];
    // CEFG results have no cases (nor strategies or counterexamples) yet
    (r.cases || []).forEach(c => items.push({ label: (c.holds ? '✔ holds' : '✘ violated') + ' in case ' + caseText(c.case), r, kind: 'case' }));
    (r.strategies || []).forEach(s => items.push({ label: 'strategy for case ' + caseText(s.case), r, kind: 'strategy', s }));
    (r.counterexamples || []).forEach(ce => items.push({ label: 'counterexample for case ' + caseText(ce.case), r, kind: 'ce', ce }));
    if (r.precondition) items.push({ label: 'weakest precondition: ' + r.precondition, r, kind: 'case' });
    $('cases').innerHTML = items.map((it, k) => `<div data-k="${k}">${escapeHtml(it.label)}</div>`).join('');
    $('cases').querySelectorAll('div').forEach(div => div.addEventListener('click', () => {
        $('cases').querySelectorAll('div').forEach(x => x.classList.remove('selected'));
        div.classList.add('selected');
        selection = items[+div.dataset.k!];
        $('explain').innerHTML = explain(game!, selection);
        drawTree();
    }));
    const firstOverlay = items.findIndex(it => it.kind !== 'case');
    selection = firstOverlay >= 0 ? items[firstOverlay] : { r, kind: 'case' };
    if (firstOverlay >= 0) $('cases').querySelectorAll('div')[firstOverlay].classList.add('selected');
    $('explain').innerHTML = explain(game!, selection);
    drawTree();
}


// ---- tree drawing -------------------------------------------------------------

// Large trees start folded at the deepest level that fits the box. Payoffs are shown under the leaves when
// that fits too; otherwise they move into the tooltip so leaves can sit NARROW_W apart.
const LEVEL_H = 90, PAD = 30, NARROW_W = 36, FOLDED_W = 70;
// histories (as JSON) of folded nodes; null makes the next drawing fold by default
let folded: Set<string> | null = null, revealed: Item | null | undefined, treeTips: string[] = [];
let foldable: { node: TreeNode, hist: Step[] }[] = [];

const histKey = (hist: unknown[]) => JSON.stringify(hist);

// a condition node of a CEFG (older versions of examples/dsl.py write "condition": "True" on every node)
const isCondition = (node: TreeNode): node is TreeNode & { condition: Condition[] } => Array.isArray(node.condition);
const isInner = (node: TreeNode) => !!node.children || isCondition(node);
// a branch below an inner node: an action, or a condition of a condition node, with the step it adds to the history
interface View {
    step: Step;
    child: TreeNode;
    cond?: Condition;
    desc?: string;
}
function branches(node: TreeNode): View[] {
    if (node.children) return node.children.map(c => ({ step: c.action, child: c.child, desc: c.description }));
    return (node.condition as Condition[]).map((c, i) => ({ step: { c: i }, child: c.child, cond: c, desc: c.description }));
}

function countLeaves(node: TreeNode): number {
    if (node._leaves === undefined)
        node._leaves = isInner(node) ? branches(node).reduce((n, c) => n + countLeaves(c.child), 0) : 1;
    return node._leaves;
}

// the leaves and folded nodes along the bottom of the drawing
function showingNodes(tree: TreeNode, folds: Set<string>) {
    const out: TreeNode[] = [];
    (function collect(node: TreeNode, hist: Step[]) {
        if (isInner(node) && !folds.has(histKey(hist))) branches(node).forEach(c => collect(c.child, hist.concat([c.step])));
        else out.push(node);
    })(tree, []);
    return out;
}

// payoffs are 12px JetBrains Mono, about 7.3px per character
function slots(showing: TreeNode[], avail: number) {
    const longest = Math.max(0, ...showing.flatMap(n => (n.utility || []).map(u => `${u.player}: ${u.value}`.length)));
    const width = (w: number) => showing.reduce((s, n) => s + (isInner(n) ? Math.max(w, FOLDED_W) : w), 2 * PAD);
    const wide = Math.max(90, longest * 7.3 + 20);
    return width(wide) <= avail ? { leafW: wide, inline: true, width: width(wide) }
                                : { leafW: NARROW_W, inline: false, width: width(NARROW_W) };
}

function defaultFolds(tree: TreeNode, avail: number) {
    const foldAt = (depth: number) => {
        const set = new Set<string>();
        (function fold(node: TreeNode, hist: Step[]) {
            if (!isInner(node)) return;
            if (hist.length === depth) { set.add(histKey(hist)); return; }
            branches(node).forEach(c => fold(c.child, hist.concat([c.step])));
        })(tree, []);
        return set;
    };
    let best = foldAt(1);
    for (let depth = 2; ; depth++) {
        const set = foldAt(depth);
        if (set.size === 0) return slots(showingNodes(tree, set), avail).width <= avail ? set : best;
        if (slots(showingNodes(tree, set), avail).width <= avail) best = set;
    }
}

// unfold one level: the node's inner children start folded
function unfoldOne(node: TreeNode, hist: Step[]) {
    folded!.delete(histKey(hist));
    branches(node).forEach(c => { if (isInner(c.child)) folded!.add(histKey(hist.concat([c.step]))); });
}

// unfold the nodes on the way to the end of `path`, keeping the branches off it folded
function unfoldPath(path: Step[]) {
    let node: TreeNode | undefined = game!.tree;
    for (let i = 0; i < path.length && node && isInner(node); i++) {
        const hist = path.slice(0, i);
        if (folded!.has(histKey(hist))) unfoldOne(node, hist);
        node = branches(node).find(c => histKey([c.step]) === histKey([path[i]]))?.child;
    }
}

// small subtrees unfold completely, larger ones a level at a time
const UNFOLD_ALL_MAX = 16;

// ' ce' or ' strategy' when a folded node hides highlighted edges
function hiddenKind(hist: Step[], h: Highlights) {
    const prefix = hist.length ? histKey(hist).slice(0, -1) + ',' : '[';
    const hides = (set: Set<string>) => [...set].some(k => k.startsWith(prefix));
    return hides(h.ce) || hides(h.ceLeaf) ? ' ce' : hides(h.strategy) ? ' strategy' : '';
}

// the unknown constants and infinitesimals of a CEFG
function unknowns() {
    return new Set([game!.constants, game!.infinitesimals].flatMap(d => (d && !Array.isArray(d) && d.unknown) || []));
}

// the unknowns that condition node `node` reveals, in its `reveals` or in its conditions, and that are not yet
// in `known` (those revealed on the way to it)
function newlyRevealed(node: TreeNode & { condition: Condition[] }, known: Set<string>) {
    const unknown = unknowns(), names = node.condition.flatMap(c => c.constraint.match(/[A-Za-z_]\w*/g) || []);
    return [...new Set([...(node.reveals || []), ...names])].filter(n => unknown.has(n) && !known.has(n));
}

// `text`: the history as shown in tooltips; `known`: the unknowns revealed on the way to `node`
interface LayoutState { next: number; maxDepth: number; leafW: number }
// `desc`: the description of the branch to `node`
function layout(node: TreeNode, depth: number, hist: Step[], text: string[], known: Set<string>, state: LayoutState, desc?: string) {
    node._hist = hist; node._text = text; node._depth = depth; node._desc = desc;
    node._folded = isInner(node) && folded!.has(histKey(hist));
    if (isCondition(node)) {
        node._revealed = newlyRevealed(node, known);
        known = new Set([...known, ...node._revealed]);
    }
    if (isInner(node) && !node._folded) {
        const bs = branches(node);
        bs.forEach(c => layout(c.child, depth + 1, hist.concat([c.step]), text.concat([c.cond ? `[${conditionText(c.cond)}]` : c.step as string]), known, state, c.desc));
        const xs = bs.map(c => c.child._x!);
        node._x = (Math.min(...xs) + Math.max(...xs)) / 2;
    } else {
        const w = node._folded ? Math.max(state.leafW, FOLDED_W) : state.leafW;
        node._x = PAD + state.next + w / 2;
        state.next += w;
    }
    state.maxDepth = Math.max(state.maxDepth, depth);
}

// the label `text` of condition `number` in `fits` characters: cut short with …, or else the number
function shorten(text: string, number: number, fits: number) {
    return text.length <= fits ? text : fits >= 8 ? text.slice(0, fits - 1) + '…' : String(number);
}

// a condition as written in the compact format, with its name if it has one
const conditionText = (c: Condition) => (c.name ? c.name + ': ' : '') + c.constraint;

function leafTip(node: TreeNode) {
    return `<div class="tip-path">${escapeHtml(node._text!.join(' ')) || '(root)'}</div>` +
        (node._desc ? `<div class="tip-path">${escapeHtml(node._desc)}</div>` : '') +
        (node.utility || []).map(u => `<div><b>${escapeHtml(u.player)}</b>: ${escapeHtml(u.value)}</div>`).join('');
}

$<SVGSVGElement>('tree').addEventListener('click', e => {
    const g = (e.target as Element).closest<SVGElement>('[data-n]');
    if (!g) return;
    const { node, hist } = foldable[+g.dataset.n!], k = histKey(hist);
    if (!folded!.has(k)) folded!.add(k);
    else if (countLeaves(node) <= UNFOLD_ALL_MAX) folded!.delete(k);
    else unfoldOne(node, hist);
    drawTree();
});
$<SVGSVGElement>('tree').addEventListener('mousemove', e => {
    const t = (e.target as Element).closest<SVGElement>('[data-tip]'), tip = $('tree-tip'), box = $('tree-box');
    if (!t) { tip.hidden = true; return; }
    tip.innerHTML = treeTips[+t.dataset.tip!];
    tip.hidden = false;
    // at most as wide as the visible part of the box (long utilities wrap); measured at its left edge, where the
    // whole width is available
    const MARGIN = 6, visible = box.clientWidth - 2 * MARGIN;
    tip.style.maxWidth = visible + 'px';
    tip.style.left = box.scrollLeft + 'px';
    const r = box.getBoundingClientRect();
    let left = e.clientX - r.left + box.scrollLeft + 14;
    // flip to the left of the pointer near the right edge, so the tooltip does not widen the scroll area,
    // and keep it inside the visible part of the box, so all of it can be read
    if (left + tip.offsetWidth > box.scrollLeft + box.clientWidth) left -= tip.offsetWidth + 28;
    left = Math.max(box.scrollLeft + MARGIN, Math.min(left, box.scrollLeft + MARGIN + visible - tip.offsetWidth));
    tip.style.left = left + 'px';
    // likewise above the pointer near the bottom, so that it does not lengthen the scroll area
    let top = e.clientY - r.top + box.scrollTop + 14;
    if (top + tip.offsetHeight > box.scrollTop + box.clientHeight) top -= tip.offsetHeight + 28;
    tip.style.top = Math.max(box.scrollTop + MARGIN, top) + 'px';
});
$<SVGSVGElement>('tree').addEventListener('mouseleave', () => { $('tree-tip').hidden = true; });
$('unfold-all').addEventListener('click', () => { folded = new Set(); revealed = selection; drawTree(); });
$('fold-default').addEventListener('click', () => { folded = null; drawTree(); });

// conditions as checkmate prints them have more parentheses, and numbers as 0.0
const sameCondition = (a: string, b: string) => {
    const norm = (s: string) => s.replace(/[\s()]/g, '').replace(/(\d)\.0+(?!\d)/g, '$1');
    return norm(a) === norm(b);
};

// add the edges of honest history `history` from `node`, reached by `hist`, to `out`; in CEFGs, it continues in every
// condition of a condition node, matched by its text, or else by its position
function honestEdges(node: TreeNode, hist: Step[], history: HistoryElement[], out: Set<string>) {
    for (const element of history) {
        if (typeof element === 'string') {
            const c = (node.children || []).find(c => c.action === element);
            if (!c) return;
            hist = hist.concat([element]);
            out.add(histKey(hist));
            node = c.child;
            continue;
        }
        if (!isCondition(node)) return;
        const cnode = node;
        element.forEach((e, i) => {
            let j = cnode.condition.findIndex(c => sameCondition(c.constraint, e.condition));
            if (j < 0 && element.length === cnode.condition.length) j = i;
            if (j < 0) return;
            const below = hist.concat([{ c: j }]);
            out.add(histKey(below));
            honestEdges(cnode.condition[j].child, below, e.path, out);
        });
        return;
    }
}

// the edges to draw highlighted, as histKey of the history up to and including them; ceLeaf: leaves of counterexamples
interface Highlights { honest: Set<string>; strategy: Set<string>; ce: Set<string>; ceLeaf: Set<string> }
function highlights(): Highlights {
    const h = { honest: new Set<string>(), strategy: new Set<string>(), ce: new Set<string>(), ceLeaf: new Set<string>() };
    const key = (hist: string[], a: string) => JSON.stringify(hist.concat([a]));
    const honest = selection ? selection.r.history : (game!.honest_histories || [])[0];
    if (honest) honestEdges(game!.tree, [], honest, h.honest);
    if (!selection) return h;
    if (selection.kind === 'strategy') selection.s!.strategy.forEach(e => h.strategy.add(key(e.history, e.action)));
    if (selection.kind === 'ce') {
        const ce = selection.ce!;
        if (selection.r.property === 'practicality') {
            // e.history ends with the deviating action, the rest of the path is how play continues practically
            ce.choices.forEach(e => {
                const path = e.history.concat(e.actions);
                path.forEach((a, i) => { if (i >= e.history.length - 1) h.ce.add(key(path.slice(0, i), a)); });
                h.ceLeaf.add(JSON.stringify(path));
            });
        } else {
            ce.choices.forEach(e => e.actions.forEach(a => h.ce.add(key(e.history, a))));
            (ce.cr_leaves || []).forEach(l => h.ceLeaf.add(JSON.stringify(l.history)));
        }
    }
    return h;
}

// players, constants and infinitesimals with a description, in the order they are declared
function showGlossary() {
    const d = game?.descriptions || {};
    const declared = (k: Declarations | undefined) => !k ? [] : Array.isArray(k) ? k : (k.known || []).concat(k.unknown || []);
    const names = game ? [...game.players, ...declared(game.constants), ...declared(game.infinitesimals)].filter(n => d[n]) : [];
    $('glossary').innerHTML = names.map(n => `<b>${escapeHtml(n)}</b> ${escapeHtml(d[n])}`).join(' &nbsp;·&nbsp; ');
}

// Players are drawn as pills with their names, cut short (with …) to what fits between the closest players on
// one level; the tooltip has the whole name. Names are 13px semibold Inter, about 8.2px per character.
const PLAYER_MAX = 14;
function playerChars(tree: Laid) {
    const levels = new Map<number, number[]>();
    (function collect(node: Laid) {
        if (!isInner(node)) return;
        if (!isCondition(node)) levels.set(node._depth, (levels.get(node._depth) || []).concat([node._x]));
        if (!node._folded) branches(node).forEach(c => collect(c.child as Laid));
    })(tree);
    let gap = Infinity;
    for (const xs of levels.values()) {
        xs.sort((a, b) => a - b);
        xs.slice(1).forEach((x, i) => { gap = Math.min(gap, x - xs[i]); });
    }
    return Math.max(1, Math.min(PLAYER_MAX, Math.floor((gap - 18) / 8.2)));
}
const playerLabel = (p: string, chars: number) => p.length <= chars ? p : chars >= 4 ? p.slice(0, chars - 1) + '…' : p.slice(0, chars);
const playerHalf = (label: string) => Math.max(14, 4.1 * label.length + 9);

// a node after layout()
type Laid = TreeNode & { _hist: Step[]; _text: string[]; _depth: number; _folded: boolean; _x: number; _revealed: string[] };

function drawTree() {
    const svg = $<SVGSVGElement>('tree');
    showGlossary();
    if (!game || !game.tree) { svg.setAttribute('width', '0'); svg.setAttribute('height', '0'); svg.innerHTML = ''; return; }
    const avail = $('tree-box').clientWidth - 2;
    if (folded === null) { folded = defaultFolds(game.tree, avail); revealed = undefined; }
    const h = highlights();
    // a newly selected result unfolds the honest history and its counterexample; strategies cover the
    // whole tree, so folds that hide them are only coloured
    if (selection !== revealed) {
        revealed = selection;
        [...h.honest, ...h.ce, ...h.ceLeaf].forEach(k => unfoldPath(JSON.parse(k)));
    }
    const { leafW, inline } = slots(showingNodes(game.tree, folded), avail);
    const state = { next: 0, maxDepth: 0, leafW };
    layout(game.tree, 0, [], [], new Set(), state);
    const chars = playerChars(game.tree as Laid);
    const treeWidth = state.next + 2 * PAD;
    const width = Math.max(treeWidth, avail);
    const shift = (width - treeWidth) / 2;
    // the rightmost point drawn beyond the layout (the unknowns revealed at a condition node), for the width
    let right = width;
    treeTips = []; foldable = [];
    // the lowest point drawn, for the height of the drawing, so that no space is left below it
    let bottom = 0;
    const y = (d: number) => PAD + 10 + d * LEVEL_H;
    // colours come from CSS classes so the tree follows the theme; labels get a halo (t-halo) in the
    // background colour so they stay readable on top of edges
    let bands = '', edges = '', labels = '', nodes = '';
    // what is drawn where, as boxes, so that condition labels beside their edges can be shortened to the space
    // they have: those are placed (in `besides`) once everything else is drawn
    const boxes: { l: number, r: number, t: number, b: number }[] = [];
    const besides: { x: number, y: number, left: boolean, text: string, number: number, tip: number }[] = [];
    const box = (l: number, r: number, t: number, b: number) => boxes.push({ l, r, t, b });
    (function draw(node: Laid) {
        const x = node._x + shift, yy = y(node._depth);
        if (isInner(node)) {
            const bs = node._folded ? [] : branches(node);
            // A condition is labelled by its name, or else its constraint (the tooltip has both). Up to three sit
            // beside their edges as actions do, as long as the space up to what is drawn next to them allows; more
            // sit just above the node they lead to, as wide as the space between those nodes. Where too little
            // would fit, the number of the condition stands in.
            const beside = bs.length <= 3;
            const gap = Math.min(...bs.slice(1).map((c, i) => c.child._x! - bs[i].child._x!));
            const fits = Math.floor((gap * 0.8) / 7.3);
            for (const c of bs) {
                const k = JSON.stringify(node._hist.concat([c.step]));
                const child = c.child as Laid, cx = child._x + shift, cy = y(child._depth);
                // the honest history is a band underneath, so strategies and counterexamples on it stay visible
                if (h.honest.has(k))
                    bands += `<line x1="${x}" y1="${yy}" x2="${cx}" y2="${cy}" class="t-band"/>`;
                const kind = h.ce.has(k) ? ' ce' : h.strategy.has(k) ? ' strategy' : h.honest.has(k) ? ' honest' : '';
                edges += `<line x1="${x}" y1="${yy}" x2="${cx}" y2="${cy}" class="t-edge${kind}"/>`;
                if (c.cond) {
                    const text = c.cond.name || c.cond.constraint, number = (c.step as { c: number }).c + 1;
                    const tip = treeTips.push(`<div class="tip-path">condition ${number}</div><div>${escapeHtml(conditionText(c.cond))}</div>` +
                        (c.desc ? `<div class="tip-path">${escapeHtml(c.desc)}</div>` : '')) - 1;
                    if (beside) {
                        besides.push({ x: (x + cx) / 2 + (cx < x ? -6 : 6), y: (yy + cy) / 2, left: cx < x, text, number, tip });
                    } else {
                        const short = shorten(text, number, fits), lx = x + (cx - x) * 0.78, ly = yy + (cy - yy) * 0.78 - 6;
                        box(lx - 3.65 * short.length, lx + 3.65 * short.length, ly - 10, ly + 3);
                        labels += `<text x="${lx}" y="${ly}" text-anchor="middle" class="t-halo t-cond" data-tip="${tip}">${escapeHtml(short)}</text>`;
                    }
                } else {
                    // action labels are 13px, about 7.8px per character
                    const action = c.step as string;
                    const lx = (x + cx) / 2 + (cx < x ? -6 : 6), ly = (yy + cy) / 2, w = 7.8 * action.length;
                    box(cx < x ? lx - w : lx, cx < x ? lx : lx + w, ly - 11, ly + 3);
                    const tip = c.desc ? ` data-tip="${treeTips.push(`<div><b>${escapeHtml(node.player)}</b> plays ${escapeHtml(action)}</div>` +
                        `<div class="tip-path">${escapeHtml(c.desc)}</div>`) - 1}"` : '';
                    labels += `<text x="${lx}" y="${ly}" font-size="13" text-anchor="${cx < x ? 'end' : 'start'}" ` +
                              `class="t-halo t-action${c.desc ? ' t-described' : ''}"${tip}>${escapeHtml(action)}</text>`;
                }
                draw(child);
            }
            const n = foldable.push({ node, hist: node._hist }) - 1;
            const reveals = isCondition(node) && node.reveals && node.reveals.length ? `reveals ${escapeHtml(node.reveals.join(', '))}, ` : '';
            const desc = !isCondition(node) && game!.descriptions?.[node.player!];
            const label = isCondition(node) ? '' : playerLabel(node.player!, chars), half = isCondition(node) ? 16 : playerHalf(label) + 2;
            const tip = treeTips.push((isCondition(node) ? 'condition node, ' + reveals
                    : `<div><b>${escapeHtml(node.player)}</b> moves${desc ? ': ' + escapeHtml(desc) : ''}</div>`) +
                `<div class="tip-path">${node._folded ? `${countLeaves(node)} leaves folded, click to unfold` : 'click to fold'}</div>`) - 1;
            nodes += `<g class="t-click" data-n="${n}" data-tip="${tip}">`;
            bottom = Math.max(bottom, yy + (node._folded ? 59 : 16));
            box(x - half, x + half, yy - 16, node._folded ? yy + 59 : yy + 16);
            if (isCondition(node) && node._revealed.length) {
                const w = 7.3 * node._revealed.join(', ').length;
                box(x + 22, x + 22 + w, yy - 9, yy + 4);
                right = Math.max(right, x + 22 + w + 10);
            }
            if (node._folded)
                nodes += `<polygon points="${x},${yy + 8} ${x - 15},${yy + 40} ${x + 15},${yy + 40}" class="t-folded${hiddenKind(node._hist, h)}"/>` +
                         `<text x="${x}" y="${yy + 55}" font-size="11" text-anchor="middle" class="t-muted">${countLeaves(node)} leaves</text>`;
            nodes += isCondition(node)
                ? `<polygon points="${x},${yy - 16} ${x + 16},${yy} ${x},${yy + 16} ${x - 16},${yy}" class="t-node t-cond-node"/>` +
                  `<text x="${x}" y="${yy + 5}" text-anchor="middle" class="t-cond-mark">?</text></g>` +
                  // what the node reveals, also in the tooltip
                  (node._revealed.length ? `<text x="${x + 22}" y="${yy + 4}" class="t-halo t-reveals">${escapeHtml(node._revealed.join(', '))}</text>` : '')
                : `<rect x="${x - half + 2}" y="${yy - 14}" width="${2 * half - 4}" height="28" rx="14" class="t-node"/>` +
                  `<text x="${x}" y="${yy + 4.5}" text-anchor="middle" class="t-player">${escapeHtml(label)}</text></g>`;
        } else if (node.subtree) {
            bottom = Math.max(bottom, yy + 32);
            box(x - 16, x + 16, yy - 14, yy + 32);
            nodes += `<polygon points="${x},${yy - 14} ${x - 16},${yy + 12} ${x + 16},${yy + 12}" class="t-subtree"/>` +
                     `<text x="${x}" y="${yy + 28}" font-size="11" text-anchor="middle" class="t-muted">subtree</text>`;
        } else {
            const mark = h.ceLeaf.has(JSON.stringify(node._hist));
            bottom = Math.max(bottom, yy + (inline ? 25 + 15 * ((node.utility || []).length - 1) : 12));
            box(x - 6, x + 6, yy - 6, yy + 6);
            // payoffs are 11px, about 6.6px per character
            if (inline && (node.utility || []).length) {
                const us = node.utility!, w = 6.6 * Math.max(...us.map(u => `${u.player}: ${u.value}`.length));
                box(x - w / 2, x + w / 2, yy + 11, yy + 25 + 15 * (us.length - 1));
            }
            nodes += `<g data-tip="${treeTips.push(leafTip(node)) - 1}">` +
                     `<rect x="${x - 12}" y="${yy - 12}" width="24" height="24" class="t-hit"/>` +
                     `<rect x="${x - 5}" y="${yy - 5}" width="10" height="10" rx="2" class="t-leaf${mark ? ' ce' : ''}"/></g>`;
            if (inline) (node.utility || []).forEach((u, i) => {
                nodes += `<text x="${x}" y="${yy + 21 + 15 * i}" font-size="11" text-anchor="middle" class="t-halo t-utility">` +
                         `<tspan>${escapeHtml(u.player)}</tspan>: ${escapeHtml(u.value)}</text>`;
            });
        }
    })(game.tree as Laid);
    // condition labels beside their edges: as far as the next box on their side of the same height, or the edge
    // of the drawing (with a little space), and at most BESIDE_MAX characters
    const BESIDE_MAX = 28;
    for (const c of besides) {
        const t = c.y - 10, b = c.y + 3;
        let room = c.left ? c.x : right - c.x;
        for (const o of boxes) {
            if (o.b < t || o.t > b) continue;
            if (c.left && o.l < c.x) room = Math.min(room, Math.max(0, c.x - o.r));
            if (!c.left && o.r > c.x) room = Math.min(room, Math.max(0, o.l - c.x));
        }
        const short = shorten(c.text, c.number, Math.min(BESIDE_MAX, Math.floor((room - 6) / 7.3)));
        const w = 7.3 * short.length;
        box(c.left ? c.x - w : c.x, c.left ? c.x : c.x + w, t, b);
        labels += `<text x="${c.x}" y="${c.y}" text-anchor="${c.left ? 'end' : 'start'}" class="t-halo t-cond" ` +
                  `data-tip="${c.tip}">${escapeHtml(short)}</text>`;
    }
    svg.setAttribute('height', String(bottom + PAD));
    svg.setAttribute('width', String(right));
    svg.innerHTML = bands + edges + labels + nodes;
}
