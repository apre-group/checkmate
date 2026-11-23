// Games described by rules: players, a state, and moves that say who may do what when, how it changes the state and
// the payoffs, and who moves next. compileRules plays out every possible play and writes the game tree in the compact
// format (see README.md), with the honest moves marked and descriptions as comments.

import { Poly, Rational } from './poly.ts';

export class RulesError extends Error {
    readonly line: number;
    constructor(line: number, message: string) {
        super(`line ${line}: ${message}`);
        this.line = line;
    }
}

export interface Compiled {
    text: string;
    // the line of the rules for each line of `text` (both counted from 1; index 0 is unused)
    lines: number[];
    leaves: number;
}

const MAX_DEPTH = 100, MAX_LEAVES = 100000;

// ---- expressions ---------------------------------------------------------------

type Expr =
    | { k: 'num', v: Rational }
    | { k: 'id', name: string }
    | { k: 'neg' | 'not', e: Expr }
    | { k: 'bin', op: string, l: Expr, r: Expr };

const KEYWORDS = new Set(['yes', 'no', 'true', 'false', 'me', 'other', 'and', 'or', 'not']);

function parseExpr(text: string, line: number): Expr {
    const tokens: string[] = [];
    const re = /\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_]\w*)|(<=|>=|!=|[-+*/()=<>]))/y;
    let pos = 0;
    while (pos < text.length) {
        if (!text.slice(pos).trim()) break;
        re.lastIndex = pos;
        const m = re.exec(text);
        if (!m) throw new RulesError(line, `unexpected "${text.slice(pos).trim()[0]}" in "${text.trim()}"`);
        tokens.push(m[1] || m[2] || m[3]);
        pos = re.lastIndex;
    }
    let i = 0;
    const peek = () => tokens[i];
    const fail = (what: string): never => {
        throw new RulesError(line, `expected ${what} in "${text.trim()}"` + (i < tokens.length ? `, got "${tokens[i]}"` : ''));
    };
    const binary = (next: () => Expr, ops: string[]) => (): Expr => {
        let l = next();
        while (ops.includes(peek())) {
            const op = tokens[i++];
            l = { k: 'bin', op, l, r: next() };
        }
        return l;
    };
    const primary = (): Expr => {
        const t = tokens[i++];
        if (t === undefined) return fail('a value');
        if (t === '(') {
            const e = or();
            if (tokens[i++] !== ')') fail('")"');
            return e;
        }
        if (t === '-') return { k: 'neg', e: primary() };
        if (/^\d/.test(t)) return { k: 'num', v: Rational.parse(t) };
        if (/^[A-Za-z_]/.test(t) && !['and', 'or', 'not'].includes(t)) return { k: 'id', name: t };
        i--;
        return fail('a value');
    };
    const product = binary(primary, ['*', '/']);
    const sum = binary(product, ['+', '-']);
    const comparison = binary(sum, ['=', '!=', '<', '<=', '>', '>=']);
    const negation = (): Expr => {
        if (peek() === 'not') { i++; return { k: 'not', e: negation() }; }
        return comparison();
    };
    const and = binary(negation, ['and']);
    const or = binary(and, ['or']);
    const e = or();
    if (i < tokens.length) fail('the end');
    return e;
}

function names(e: Expr, out: string[] = []): string[] {
    if (e.k === 'id') out.push(e.name);
    else if (e.k === 'neg' || e.k === 'not') names(e.e, out);
    else if (e.k === 'bin') { names(e.l, out); names(e.r, out); }
    return out;
}

// ---- parsing --------------------------------------------------------------------

interface Clause<T> { value: T; line: number }

interface Move {
    name: string;
    players: string[];
    honest: boolean;
    description: string;
    line: number;
    conditions: Clause<Expr>[];
    sets: Clause<{ name: string, e: Expr }>[];
    pays: Clause<{ who: string, e: Expr }>[];
    next?: Clause<Expr>;
    end?: number;
}

interface Rules {
    header: { text: string, line: number }[];
    players: string[];
    symbols: Set<string>;  // constants and infinitesimals
    start: Clause<string>;
    state: Map<string, Clause<Expr>>;
    moves: Move[];
}

const PASS_THROUGH = ['initial', 'weak_immunity', 'weaker_immunity', 'collusion_resilience', 'practicality'];

function splitTop(text: string) { return text.split(',').map(s => s.trim()); }

function parseRules(source: string): Rules {
    const rules: Rules = { header: [], players: [], symbols: new Set(), start: { value: '', line: 0 }, state: new Map(), moves: [] };
    let move: Move | null = null;
    source.split('\n').forEach((raw, k) => {
        const line = k + 1;
        const hash = raw.indexOf('#');
        const code = hash < 0 ? raw : raw.slice(0, hash);
        const description = hash < 0 ? '' : raw.slice(hash + 1).trim();
        if (!code.trim()) return;
        if (code.includes('\t')) throw new RulesError(line, 'use spaces, not tabs');
        const body = code.trim();
        if (/^\s/.test(code)) {
            if (!move) throw new RulesError(line, 'an indented line must belong to a move');
            parseClause(move, body, line);
            return;
        }
        const m = body.match(/^(honest\s+)?move\s+(\S+)\s+by\s+(.+)$/);
        if (m) {
            if (!/^[A-Za-z_]\w*$/.test(m[2])) throw new RulesError(line, `bad move name "${m[2]}": use letters, digits and _`);
            move = { name: m[2], players: splitTop(m[3]), honest: !!m[1], description, line, conditions: [], sets: [], pays: [] };
            rules.moves.push(move);
            return;
        }
        if (/^(honest\s+)?move\b/.test(body)) throw new RulesError(line, 'expected move NAME by PLAYER, ...');
        move = null;
        const header = body.match(/^([A-Za-z_]+)\s*:\s*(.*)$/);
        if (!header) throw new RulesError(line, `expected a setting (KEY: value) or a move, got "${body}"`);
        const [, key, value] = header;
        if (key === 'players' || key === 'constants' || key === 'infinitesimals') {
            for (const n of splitTop(value)) {
                if (!/^[A-Za-z_]\w*$/.test(n)) throw new RulesError(line, `bad name "${n}" in ${key}`);
                if (key === 'players') rules.players.push(n);
                else rules.symbols.add(n);
            }
            rules.header.push({ text: raw.trimEnd(), line });
        } else if (PASS_THROUGH.includes(key)) {
            rules.header.push({ text: raw.trimEnd(), line });
        } else if (key === 'start') {
            rules.start = { value: value.trim(), line };
        } else if (key === 'state') {
            for (const part of splitTop(value)) {
                const a = part.match(/^([A-Za-z_]\w*)\s*=\s*(.+)$/);
                if (!a) throw new RulesError(line, `expected NAME = value in state, got "${part}"`);
                if (rules.state.has(a[1])) throw new RulesError(line, `${a[1]} is in the state twice`);
                rules.state.set(a[1], { value: parseExpr(a[2], line), line });
            }
        } else if (key === 'honest') {
            throw new RulesError(line, 'mark the honest moves with "honest move" instead of honest: lines');
        } else {
            throw new RulesError(line, `unknown setting "${key}"`);
        }
    });
    return rules;
}

function parseClause(move: Move, body: string, line: number) {
    const [, word, rest = ''] = body.match(/^(\S+)\s*(.*)$/)!;
    if (word === 'if') {
        move.conditions.push({ value: parseExpr(rest, line), line });
    } else if (word === 'set') {
        for (const part of splitTop(rest)) {
            const a = part.match(/^([A-Za-z_]\w*)\s*=\s*(.+)$/);
            if (!a) throw new RulesError(line, `expected set NAME = value, got "${part}"`);
            move.sets.push({ value: { name: a[1], e: parseExpr(a[2], line) }, line });
        }
    } else if (word === 'pay') {
        for (const part of splitTop(rest)) {
            const a = part.match(/^([A-Za-z_]\w*)\s*:\s*(.+)$/);
            if (!a) throw new RulesError(line, `expected pay PLAYER: amount, got "${part}"`);
            move.pays.push({ value: { who: a[1], e: parseExpr(a[2], line) }, line });
        }
    } else if (word === 'next') {
        if (move.next || move.end) throw new RulesError(line, `move ${move.name} already says what comes next`);
        move.next = { value: parseExpr(rest, line), line };
    } else if (word === 'end') {
        if (move.next || move.end) throw new RulesError(line, `move ${move.name} already says what comes next`);
        if (rest) throw new RulesError(line, 'end takes nothing after it');
        move.end = line;
    } else {
        throw new RulesError(line, `expected if, set, pay, next or end, got "${word}"`);
    }
}

// ---- checks ---------------------------------------------------------------------

function check(rules: Rules) {
    const { players, symbols, state } = rules;
    if (!players.length) throw new RulesError(1, 'the game needs a players: line');
    if (!rules.start.line) rules.start = { value: players[0], line: rules.header[0].line };
    if (!players.includes(rules.start.value)) throw new RulesError(rules.start.line, `${rules.start.value} is not a player`);
    if (!rules.moves.length) throw new RulesError(rules.start.line, 'the game needs moves: move NAME by PLAYER');
    for (const [name, c] of state) {
        if (players.includes(name) || symbols.has(name) || KEYWORDS.has(name))
            throw new RulesError(c.line, `the state cannot be called ${name}: that is a player, constant or keyword`);
    }
    // the values that names in the state take (e.g. phase = open), so that a misspelled one is caught
    const values = new Set<string>();
    const value = (e: Expr) => { if (e.k === 'id' && !state.has(e.name) && !KEYWORDS.has(e.name)) values.add(e.name); };
    for (const c of state.values()) value(c.value);
    for (const m of rules.moves) for (const s of m.sets) value(s.value.e);
    const known = (name: string, line: number, me: boolean) => {
        if ((name === 'me' || name === 'other') && !me) throw new RulesError(line, `${name} only makes sense in a move`);
        if (name === 'other' && players.length !== 2) throw new RulesError(line, 'other only makes sense with two players');
        if (symbols.has(name)) throw new RulesError(line, `${name} is a constant: it can only be paid, not used in the state`);
        if (!state.has(name) && !players.includes(name) && !KEYWORDS.has(name) && !values.has(name))
            throw new RulesError(line, `unknown name ${name}`);
    };
    for (const c of state.values()) for (const n of names(c.value)) known(n, c.line, false);
    for (const m of rules.moves) {
        for (const p of m.players)
            if (!players.includes(p)) throw new RulesError(m.line, `${p} is not a player`);
        if (!m.next && !m.end) throw new RulesError(m.line, `move ${m.name} needs "next PLAYER" or "end" below it`);
        for (const c of [...m.conditions, ...(m.next ? [m.next] : [])]) for (const n of names(c.value)) known(n, c.line, true);
        for (const s of m.sets) {
            if (!state.has(s.value.name)) throw new RulesError(s.line, `${s.value.name} is not in the state (add it to a state: line)`);
            for (const n of names(s.value.e)) known(n, s.line, true);
        }
        for (const p of m.pays) {
            const who = p.value.who;
            if (!players.includes(who) && who !== 'me' && who !== 'other') throw new RulesError(p.line, `${who} is not a player`);
            if (who === 'other' && players.length !== 2) throw new RulesError(p.line, 'other only makes sense with two players');
            for (const n of names(p.value.e))
                if (!symbols.has(n) && !state.has(n))
                    throw new RulesError(p.line, `${n} in a payoff must be a constant, an infinitesimal, or a number in the state`);
        }
    }
}

// ---- playing it out ---------------------------------------------------------------

type Value = boolean | Rational | string;

interface Position {
    turn: string;
    state: Map<string, Value>;
    payoffs: Poly[];
}

function show(v: Value) { return v instanceof Rational ? v.decimal() ?? `${v.n}/${v.d}` : String(v); }

function evaluate(e: Expr, pos: Position, players: string[], line: number, where: string): Value {
    const ev = (e: Expr): Value => evaluate(e, pos, players, line, where);
    const fail = (message: string): never => { throw new RulesError(line, message + where); };
    const number = (v: Value) => v instanceof Rational ? v : fail(`${show(v)} is not a number`);
    const bool = (v: Value) => typeof v === 'boolean' ? v : fail(`${show(v)} is not yes or no`);
    switch (e.k) {
        case 'num': return e.v;
        case 'id':
            if (pos.state.has(e.name)) return pos.state.get(e.name)!;
            if (e.name === 'yes' || e.name === 'true') return true;
            if (e.name === 'no' || e.name === 'false') return false;
            if (e.name === 'me') return pos.turn;
            if (e.name === 'other') return players.find(p => p !== pos.turn)!;
            return e.name;
        case 'neg': return number(ev(e.e)).neg();
        case 'not': return !bool(ev(e.e));
        case 'bin': {
            if (e.op === 'and') return bool(ev(e.l)) && bool(ev(e.r));
            if (e.op === 'or') return bool(ev(e.l)) || bool(ev(e.r));
            const l = ev(e.l), r = ev(e.r);
            if (e.op === '=' || e.op === '!=') {
                if (typeof l !== typeof r || (l instanceof Rational) !== (r instanceof Rational))
                    fail(`cannot compare ${show(l)} with ${show(r)}`);
                const same = l instanceof Rational ? l.n === (r as Rational).n && l.d === (r as Rational).d : l === r;
                return e.op === '=' ? same : !same;
            }
            const a = number(l), b = number(r);
            switch (e.op) {
                case '+': return a.add(b);
                case '-': return a.add(b.neg());
                case '*': return a.mul(b);
                case '/': return b.isZero() ? fail('division by zero') : a.div(b);
            }
            const diff = a.add(b.neg()).n;
            return e.op === '<' ? diff < 0n : e.op === '<=' ? diff <= 0n : e.op === '>' ? diff > 0n : diff >= 0n;
        }
    }
}

function payoff(e: Expr, pos: Position, symbols: Set<string>, line: number, where: string): Poly {
    const ev = (e: Expr): Poly => payoff(e, pos, symbols, line, where);
    switch (e.k) {
        case 'num': return Poly.constant(e.v);
        case 'id': {
            if (symbols.has(e.name)) return Poly.symbol(e.name);
            const v = pos.state.get(e.name);
            if (!(v instanceof Rational)) throw new RulesError(line, `${e.name} is ${show(v!)}, not a number${where}`);
            return Poly.constant(v);
        }
        case 'neg': return ev(e.e).neg();
        case 'not': throw new RulesError(line, 'not in a payoff');
        case 'bin': {
            const l = ev(e.l), r = ev(e.r);
            if (e.op === '+') return l.add(r);
            if (e.op === '-') return l.add(r.neg());
            if (e.op === '*') return l.mul(r);
            if (e.op === '/') {
                const c = r.asConstant();
                if (!c || c.isZero()) throw new RulesError(line, 'a payoff can only be divided by a number other than 0');
                return l.mul(Poly.constant(new Rational(c.d, c.n)));
            }
            throw new RulesError(line, `${e.op} in a payoff`);
        }
    }
}

export function compileRules(source: string): Compiled {
    const rules = parseRules(source);
    check(rules);
    const { players, symbols } = rules;
    const out: string[] = [], lines: number[] = [0];
    const emit = (text: string, line: number) => { out.push(text); lines.push(line); };
    for (const h of rules.header) emit(h.text, h.line);
    emit('', rules.start.line);

    const initial: Position = { turn: rules.start.value, state: new Map(), payoffs: players.map(() => new Poly()) };
    for (const [name, c] of rules.state) initial.state.set(name, evaluate(c.value, initial, players, c.line, ''));

    let leaves = 0;
    const after = (history: string[]) => history.length ? ` (after ${history.join(' ')})` : ' (at the start)';
    // the lines below the node at `pos`; `line`: the rules line that led there; `honest`: on an honest history
    const play = (pos: Position, history: string[], indent: string, line: number, honest: boolean) => {
        if (history.length >= MAX_DEPTH)
            throw new RulesError(line, `the game does not end within ${MAX_DEPTH} moves: ${history.slice(0, 12).join(' ')} ...`);
        const where = after(history);
        const possible = rules.moves.filter(m => m.players.includes(pos.turn) &&
            m.conditions.every(c => {
                const v = evaluate(c.value, pos, players, c.line, where);
                if (typeof v !== 'boolean') throw new RulesError(c.line, `the condition is ${show(v)}, not yes or no${where}`);
                return v;
            }));
        if (!possible.length)
            throw new RulesError(line, `${pos.turn} moves next${where}, but none of their moves is possible`);
        const seen = new Set<string>();
        for (const m of possible) {
            if (seen.has(m.name)) throw new RulesError(m.line, `two moves ${m.name} are possible at once${where}`);
            seen.add(m.name);
        }
        if (honest && !possible.some(m => m.honest))
            throw new RulesError(line, `the honest play reaches ${pos.turn}${where}, but none of their possible moves ` +
                `(${possible.map(m => m.name).join(', ')}) is honest`);
        for (const m of possible) {
            const state = new Map(pos.state);
            for (const s of m.sets) state.set(s.value.name, evaluate(s.value.e, pos, players, s.line, where));
            const payoffs = pos.payoffs.slice();
            for (const p of m.pays) {
                const who = p.value.who === 'me' ? pos.turn : p.value.who === 'other' ? players.find(q => q !== pos.turn)! : p.value.who;
                const i = players.indexOf(who);
                payoffs[i] = payoffs[i].add(payoff(p.value.e, pos, symbols, p.line, where));
            }
            const mark = honest && m.honest ? 'honest ' : '', description = m.description ? '  # ' + m.description : '';
            if (m.end) {
                if (++leaves > MAX_LEAVES) throw new RulesError(m.line, `the game has more than ${MAX_LEAVES} ways to end`);
                let text;
                try {
                    text = players.map((p, i) => `${p}: ${payoffs[i]}`).join(', ');
                } catch (err) {
                    throw new RulesError(m.line, (err as Error).message + after(history.concat([m.name])));
                }
                emit(`${indent}${mark}${m.name} -> ${text}${description}`, m.line);
                continue;
            }
            const next = evaluate(m.next!.value, { ...pos, state }, players, m.next!.line, where);
            if (typeof next !== 'string' || !players.includes(next))
                throw new RulesError(m.next!.line, `${show(next)} is not a player${where}`);
            emit(`${indent}${mark}${m.name} -> ${next}${description}`, m.line);
            play({ turn: next, state, payoffs }, history.concat([m.name]), indent + '  ', m.line, honest && m.honest);
        }
    };
    emit(rules.start.value, rules.start.line);
    play(initial, [], '  ', rules.start.line, true);
    return { text: out.join('\n') + '\n', lines, leaves };
}

// does this text look like rules rather than a game tree?
export const looksLikeRules = (text: string) => /^(honest\s+)?move\s/m.test(text);
