// Random games for the web page, a port of scripts/gen_game.py. Constraints are kept satisfiable
// by construction: every atom is checked against a random witness point instead of a solver.

function makeRng(seed) {
    // mulberry32
    let a = seed >>> 0;
    const next = () => {
        a = (a + 0x6D2B79F5) >>> 0;
        let t = a;
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    return {
        random: next,
        int: (lo, hi) => lo + Math.floor(next() * (hi - lo + 1)),
        choice: xs => xs[Math.floor(next() * xs.length)],
        sample: (xs, k) => {
            const ys = xs.slice();
            for (let i = ys.length - 1; i > 0; i--) {
                const j = Math.floor(next() * (i + 1));
                [ys[i], ys[j]] = [ys[j], ys[i]];
            }
            return ys.slice(0, k);
        },
    };
}

// A linear term as a string and as coefficients, so it can be evaluated at the witness.
function linTerm(rng, names, maxCoef, constRange, nonneg) {
    const c = rng.int(nonneg ? 0 : -constRange, constRange);
    const coefs = {};
    const parts = [];
    if (c !== 0 || rng.random() < 0.3) parts.push(String(c));
    for (const n of names) {
        if (rng.random() < 0.5) continue;
        const k = rng.int(nonneg ? 0 : -maxCoef, maxCoef);
        if (k === 0) continue;
        coefs[n] = k;
        parts.push(k === 1 ? n : k === -1 ? '-' + n : k + '*' + n);
    }
    let s = parts.length ? parts[0] : '0';
    for (const p of parts.slice(1)) s += p.startsWith('-') ? ' - ' + p.slice(1) : ' + ' + p;
    return { text: s, value: w => c + Object.entries(coefs).reduce((acc, [n, k]) => acc + k * w[n], 0) };
}

const SIZES = {
    small: { weight: 0.4, players: [2, 3], depth: [1, 3], branch: [2, 3], stop: 0.3 },
    medium: { weight: 0.45, players: [2, 4], depth: [2, 4], branch: [2, 3], stop: 0.25 },
    large: { weight: 0.15, players: [3, 5], depth: [3, 5], branch: [2, 3], stop: 0.2 },
};

const COMPARE = { '<': (a, b) => a < b, '<=': (a, b) => a <= b, '>': (a, b) => a > b,
                  '>=': (a, b) => a >= b, '=': (a, b) => a === b, '!=': (a, b) => a !== b };

function genGame(seed) {
    const rng = makeRng(seed);
    let r = rng.random(), size = 'large';
    for (const [name, s] of Object.entries(SIZES)) { if ((r -= s.weight) < 0) { size = name; break; } }
    const S = SIZES[size];
    const players = ['A', 'B', 'C', 'D', 'E'].slice(0, rng.int(...S.players));
    const constants = Array.from({ length: rng.int(1, 3) }, (_, i) => 'c' + i);
    const infinitesimals = Array.from({ length: rng.choice([0, 0, 1, 2]) }, (_, i) => 'e' + i);
    const maxBranch = rng.int(...S.branch);
    const actions = ['x', 'y', 'z', 'w'].slice(0, maxBranch);
    const depth = rng.int(...S.depth);
    const posRate = rng.choice([0, 0.5, 0.9, 1]);

    // infinitesimals only matter when real parts tie, so real parts often come from a small pool
    let realPool = null, infRate = 0.4;
    if (infinitesimals.length && rng.random() < 0.7) {
        realPool = ['0'].concat(Array.from({ length: rng.int(1, 2) },
            () => linTerm(rng, constants, 2, 3, rng.random() < posRate).text));
        infRate = 0.8;
    }
    const term = () => {
        const nonneg = rng.random() < posRate;
        let s = realPool ? rng.choice(realPool) : linTerm(rng, constants, 2, 3, nonneg).text;
        if (infinitesimals.length && rng.random() < infRate) {
            const inf = linTerm(rng, infinitesimals, 2, 0, nonneg && rng.random() < 0.5).text;
            if (inf !== '0') s = s + ' + (' + inf + ')';
        }
        return s;
    };
    const newLeaf = () => players.map(p => ({ player: p, value: term() }));
    const genTree = (d, root) => {
        if (!root && (d === 0 || rng.random() < S.stop)) return { utility: newLeaf() };
        const n = rng.int(root ? 2 : 1, maxBranch);
        return { player: rng.choice(players),
                 children: rng.sample(actions, n).map(a => ({ action: a, child: genTree(d - 1, false) })) };
    };
    const tree = genTree(depth, true);

    // constraints: atoms that hold at a random witness point, so they are satisfiable together
    const witness = {};
    constants.forEach(c => { witness[c] = rng.int(posRate > 0 ? 1 : -3, 5); });
    infinitesimals.forEach(e => { witness[e] = rng.int(1, 3); });
    const atom = () => {
        for (let tries = 0; tries < 50; tries++) {
            const op = rng.choice(Object.keys(COMPARE));
            const l = linTerm(rng, constants, 2, 2, false), rr = linTerm(rng, constants, 2, 2, false);
            if (COMPARE[op](l.value(witness), rr.value(witness))) return `${l.text} ${op} ${rr.text}`;
        }
        return null;
    };
    const initial = constants.concat(infinitesimals).filter(c => witness[c] > 0 && rng.random() < 0.7).map(c => c + ' > 0');
    for (let i = rng.int(0, 2); i > 0; i--) { const a = atom(); if (a) initial.push(a); }
    const props = {};
    for (const p of ['weak_immunity', 'weaker_immunity', 'collusion_resilience', 'practicality']) {
        const a = rng.random() < 0.25 ? atom() : null;
        props[p] = a ? [a] : [];
    }

    const histories = [];
    (function leaves(t, h) {
        if (t.utility) { histories.push(h); return; }
        t.children.forEach(c => leaves(c.child, h.concat([c.action])));
    })(tree, []);
    const longest = Math.max(...histories.map(h => h.length));
    const candidates = rng.random() < 0.6 ? histories.filter(h => h.length >= longest - 1) : histories;
    const honest = rng.sample(candidates, Math.min(candidates.length, rng.choice([1, 1, 2])));
    // random leaves rarely make the honest history secure: favour it sometimes so YES answers occur
    if (rng.random() < 0.6) {
        for (const h of honest) {
            let node = tree;
            for (const a of h) node = node.children.find(c => c.action === a).child;
            node.utility.forEach(u => { u.value = u.value + ' + 4'; });
        }
    }
    return { players, actions, infinitesimals, constants, initial_constraints: initial,
             property_constraints: props, honest_histories: honest, tree };
}
