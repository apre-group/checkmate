import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { compileRules, looksLikeRules, RulesError } from '../../html/src/rules.ts';

// the tree part of the compiled game: the lines after the blank line that ends the header
const tree = (source: string) => compileRules(source).text.split('\n\n')[1].trimEnd();

const fails = (source: string, line: number, message: RegExp) => assert.throws(() => compileRules(source), (e: unknown) => {
    assert.ok(e instanceof RulesError, String(e));
    assert.equal(e.line, line, e.message);
    assert.match(e.message, message);
    return true;
});

test('a game without state', () => {
    assert.equal(tree(`players: A, B
honest move go by A
  next B
honest move stop by B
  pay A: 1, B: 2
  end
move quit by A
  end
`), `A
  honest go -> B
    honest stop -> A: 1, B: 2
  quit -> A: 0, B: 0`);
});

test('the header is copied, comments and all, and start defaults to the first player', () => {
    const { text } = compileRules(`# a comment
players: A  # the first
players: B
constants: x, y
infinitesimals: e
initial: x > y
practicality: x > 0
honest move go by A
  end
`);
    assert.equal(text, `players: A  # the first
players: B
constants: x, y
infinitesimals: e
initial: x > y
practicality: x > 0

A
  honest go -> A: 0, B: 0
`);
});

test('the lines of the rules that each line of the tree comes from', () => {
    const source = `players: A, B
start: B

honest move go by B  # line 4
  next A
honest move stop by A
  end
`;
    const { text, lines } = compileRules(source);
    const at = (s: string) => lines[text.split('\n').findIndex(l => l.includes(s)) + 1];
    assert.equal(at('players'), 1);
    assert.equal(at('honest go'), 4);
    assert.equal(at('honest stop'), 6);
    assert.equal(lines[text.split('\n').indexOf('B') + 1], 2);
});

test('honest moves are marked only along the honest plays', () => {
    assert.equal(tree(`players: A, B
honest move fair by A
  next B
move cheat by A
  next B
honest move accept by B
  end
`), `A
  honest fair -> B
    honest accept -> A: 0, B: 0
  cheat -> B
    accept -> A: 0, B: 0`);
});

test('several honest moves give several honest plays', () => {
    const source = `players: A, B
honest move x by A
  end
honest move y by A
  end
`;
    assert.equal(tree(source), `A
  honest x -> A: 0, B: 0
  honest y -> A: 0, B: 0`);
});

test('state, conditions and changes', () => {
    assert.equal(tree(`players: A, B
constants: c
state: n = 0, open = yes, phase = start

honest move step by A, B
  if open and n < 2
  set n = n + 1, phase = middle
  pay me: c
  next other

honest move close by A, B
  if n = 2 and not (phase = start)
  set open = no
  pay A: n * c
  end
`), `A
  honest step -> B
    honest step -> A
      honest close -> A: 3 * c, B: c`);
});

test('set uses the state before the move', () => {
    assert.equal(tree(`players: A, B
state: a = 1, b = 2
honest move swap by A
  set a = b, b = a
  next B
honest move show by B
  if a = 2 and b = 1
  end
`), `A
  honest swap -> B
    honest show -> A: 0, B: 0`);
});

test('next can be any expression that gives a player', () => {
    assert.equal(tree(`players: A, B, C
state: last = C
honest move go by A
  if last = C
  set last = A
  next last
honest move stop by A
  if last = A
  end
`), `A
  honest go -> A
    honest stop -> A: 0, B: 0, C: 0`);
});

test('descriptions follow the moves', () => {
    assert.equal(tree(`players: A, B
honest move go by A  # goes on
  next B
honest move stop by B  # ends it
  end
`), `A
  honest go -> B  # goes on
    honest stop -> A: 0, B: 0  # ends it`);
});

test('payoffs are simplified', () => {
    assert.equal(tree(`players: A, B
constants: x
infinitesimals: e
honest move go by A
  pay A: x / 2 + e, B: x - x
  next B
honest move stop by B
  pay A: x / 2 - 2 * e, B: -(x - 1) * 2
  end
`), `A
  honest go -> B
    honest stop -> A: x - e, B: -2 * x + 2`);
});

test('errors in the rules', () => {
    fails('players: A\n\thonest move go by A\n', 2, /tabs/);
    fails('players: A\n  if x\n', 2, /must belong to a move/);
    fails('players: A\nhonest move 1go by A\n  end\n', 2, /bad move name/);
    fails('players: A\nmove go\n', 2, /expected move NAME by PLAYER/);
    fails('players: A\nwhatever: 1\nhonest move go by A\n  end\n', 2, /unknown setting/);
    fails('players: A\nthis is not a setting\n', 2, /expected a setting/);
    fails('players: A\nstate: n = 1, n = 2\nhonest move go by A\n  end\n', 2, /twice/);
    fails('players: A\nstate: A = 1\nhonest move go by A\n  end\n', 2, /cannot be called A/);
    fails('constants: c\nhonest move go by A\n  end\n', 1, /needs a players: line/);
    fails('players: A\nstart: B\nhonest move go by A\n  end\n', 2, /B is not a player/);
    fails('players: A\n', 1, /needs moves/);
    fails('players: A\nhonest move go by B\n  end\n', 2, /B is not a player/);
    fails('players: A\nhonest move go by A\n  set n = 1\n  end\n', 3, /not in the state/);
    fails('players: A\nstate: n = me\nhonest move go by A\n  end\n', 2, /only makes sense in a move/);
    fails('players: A, B, C\nhonest move go by A\n  next other\n', 3, /two players/);
    fails('players: A, B, C\nhonest move go by A\n  pay other: 1\n  end\n', 3, /two players/);
    fails('players: A\nconstants: c\nhonest move go by A\n  if c > 0\n  end\n', 4, /constant/);
    fails('players: A\nhonest move go by A\n  end now\n', 3, /end takes nothing/);
    fails('players: A\nhonest move go by A\n  end\n  next A\n', 4, /already says what comes next/);
    fails('players: A\nhonest move go by A\n  jump\n', 3, /expected if, set, pay, next or end/);
    fails('players: A\nhonest move go by A\n  set x\n', 3, /expected set NAME = value/);
    fails('players: A\nhonest move go by A\n  pay A 1\n  end\n', 3, /expected pay PLAYER: amount/);
    fails('players: A\nhonest move go by A\n  if (yes\n  end\n', 3, /expected "\)"/);
    fails('players: A\nhonest move go by A\n  if yes yes\n  end\n', 3, /expected the end/);
    fails('players: A\nhonest move go by A\n  if 1 $ 2\n  end\n', 3, /unexpected "\$"/);
    fails('players: A\nhonest: go\nhonest move go by A\n  end\n', 2, /honest move/);
});

test('errors while playing the game out', () => {
    fails('players: A\nstate: n = 1\nhonest move go by A\n  if n\n  end\n', 4, /not yes or no \(at the start\)/);
    fails('players: A\nstate: n = 1\nhonest move go by A\n  if n = yes\n  end\n', 4, /cannot compare 1 with true/);
    fails('players: A\nstate: n = 1\nhonest move go by A\n  if n + yes > 0\n  end\n', 4, /true is not a number/);
    fails('players: A\nstate: n = 0\nhonest move go by A\n  set n = 1 / n\n  end\n', 4, /division by zero/);
    fails('players: A\nstate: n = 0, p = q\nhonest move go by A\n  next p\n', 4, /q is not a player/);
    fails('players: A\nstate: b = yes\nhonest move go by A\n  pay A: b\n  end\n', 4, /b is true, not a number/);
    fails('players: A\nconstants: c\nhonest move go by A\n  pay A: 1 / c\n  end\n', 4, /divided by a number/);
    fails('players: A\nconstants: c\nhonest move go by A\n  pay A: c / 3\n  end\n', 3, /1\/3/);
    fails('players: A\nstate: n = 2\nhonest move square by A\n  set n = n * n\n  next A\n', 4, /larger than 2\^64 \(after square square square square square square\)/);
    fails('players: A\nstate: n = 1\nhonest move halve by A\n  set n = n / 3\n  next A\n', 4, /larger than 2\^64/);
});

test('every example compiles', () => {
    for (const name of ['loan', 'loan_with_deposit', 'market_entry', 'closing_channel', 'centipede']) {
        const { text, leaves } = compileRules(readFileSync(`examples/readable/${name}.rules`, 'utf8'));
        assert.ok(leaves > 0 && text.includes('honest'), name);
    }
});

test('rules are told apart from game trees', () => {
    assert.ok(looksLikeRules('players: A\nmove go by A\n  end\n'));
    assert.ok(looksLikeRules('players: A\nhonest move go by A\n  end\n'));
    assert.ok(!looksLikeRules('players: A\n\nA\n  honest move -> A: 1\n'));
    assert.ok(!looksLikeRules('players: A\n\nA\n  movement -> A: 1\n'));
});
