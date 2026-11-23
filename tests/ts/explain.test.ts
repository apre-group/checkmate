import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { explain, type Item } from '../../html/src/explain.ts';
import type { Game, Result } from '../../html/src/game.ts';

// examples/readable/market_entry.game, and checkmate's results for it with --strategies --counterexamples
const game: Game = JSON.parse(readFileSync('tests/ts/fixtures/market_entry.game.json', 'utf8'));
const results: Result[] = JSON.parse(readFileSync('tests/ts/fixtures/market_entry.results.json', 'utf8')).results;

const result = (property: string, history: string[]) => {
    const r = results.find(r => r.property === property && JSON.stringify(r.history) === JSON.stringify(history));
    assert.ok(r, `${property} for ${history}`);
    return r;
};
// what the page shows first for a result: its strategy or counterexample
const first = (r: Result): Item => r.strategies?.length ? { r, kind: 'strategy', s: r.strategies[0] }
    : r.counterexamples?.length ? { r, kind: 'ce', ce: r.counterexamples[0] } : { r, kind: 'case' };
const text = (html: string) => html.replace(/<[^>]*>/g, '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
const words = (property: string, history: string[]) => text(explain(game, first(result(property, history))));

test('a property that holds, with its strategy', () => {
    const w = words('weak_immunity', ['stay_out']);
    assert.match(w, /^Weak immunity: A player who plays honestly never ends up with a negative payoff/);
    assert.match(w, /Yes, for the honest history stay_out\./);
    assert.match(w, /Newcomer plays stay_out at the start/);
    assert.match(w, /Incumbent plays share after enter/);
    assert.match(w, /The other actions can be anything\./);
});

test('collusion resilience and practicality strategies do not leave actions open', () => {
    assert.doesNotMatch(words('collusion_resilience', ['stay_out']), /can be anything/);
    assert.doesNotMatch(words('practicality', ['enter', 'share']), /can be anything/);
});

test('a weak immunity counterexample', () => {
    const w = words('weak_immunity', ['enter', 'share']);
    assert.match(w, /No, not for the honest history enter → share\./);
    assert.match(w, /Newcomer can end up with a negative payoff while playing honestly, if/);
    assert.match(w, /Incumbent plays fight after enter/);
});

test('weaker immunity ignores infinitesimals', () => {
    assert.match(words('weaker_immunity', ['enter', 'share']), /negative payoff \(apart from infinitesimals\)/);
});

test('a collusion resilience counterexample, with the payoffs it compares', () => {
    const w = words('collusion_resilience', ['enter', 'fight']);
    assert.match(w, /Deviating from the honest history pays off/);
    assert.match(w, /Incumbent deviates to share after enter/);
    assert.match(w, /The game then ends at enter → share, where Incumbent gets profit instead of -war_cost on the honest history\./);
});

test('a practicality counterexample, with the payoffs it compares', () => {
    const w = words('practicality', ['stay_out']);
    assert.match(w, /Newcomer is better off playing enter at the start instead of following the honest history\./);
    assert.match(w, /enter → share, where Newcomer gets profit instead of 0 on the honest history/);
    assert.match(words('practicality', ['enter', 'fight']), /Incumbent is better off playing share after enter/);
});

test('a case alone gives the meaning and the verdict', () => {
    const r = result('weak_immunity', ['stay_out']);
    assert.equal(text(explain(game, { r, kind: 'case' })).split('Yes')[1], ', for the honest history stay_out.');
});

test('cases, preconditions and undecided results', () => {
    const r: Result = { property: 'practicality', history: ['enter', 'share'], holds: false,
        cases: [{ case: ['profit > 1'], holds: true }, { case: ['profit <= 1'], holds: false }], precondition: 'profit > 1' };
    const w = text(explain(game, { r, kind: 'case' }));
    assert.match(w, /it holds in some of the cases below, but not in all/);
    assert.match(w, /It holds exactly when profit > 1 \(the weakest precondition\)/);
    const undecided: Result = { property: 'practicality', holds: null, undecided: 'neither Z3 nor cvc5 could decide it' };
    assert.match(text(explain(game, { r: undecided, kind: 'case' })), /could not decide this for this run: neither Z3 nor cvc5/);
    const all: Result = { property: 'weak_immunity', history: ['stay_out'], holds: true,
        cases: [{ case: ['profit > 1'], holds: true }, { case: ['profit <= 1'], holds: true }] };
    assert.match(text(explain(game, { r: all, kind: 'case' })), /in every case below/);
});

test('a counterexample in a case says so', () => {
    const r = result('weak_immunity', ['enter', 'share']);
    const ce = { ...r.counterexamples![0], case: ['profit > war_cost'] };
    assert.match(text(explain(game, { r, kind: 'ce', ce })), /while playing honestly when profit > war_cost, if/);
});

test('names are escaped', () => {
    const r: Result = { property: 'weak_immunity', history: ['<a>'], holds: true,
        strategies: [{ case: [], strategy: [{ player: 'P&Q', history: [], action: '<a>' }] }] };
    const html = explain(game, first(r));
    assert.ok(!html.includes('<a>') && html.includes('&lt;a&gt;') && html.includes('P&amp;Q'), html);
});
