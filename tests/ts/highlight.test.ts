import { test } from 'node:test';
import assert from 'node:assert/strict';
import { highlightCompact, highlightRules } from '../../html/src/highlight.ts';

const unhighlight = (html: string) =>
    html.replace(/<[^>]*>/g, '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
// the classes of the spans around `text`
const classes = (html: string, text: string) =>
    [...html.matchAll(/<span class="([^"]*)">([^<]*)<\/span>/g)].filter(m => m[2] === text).map(m => m[1]);

const COMPACT = `players: A, B  # the players
constants: x
initial: x > 0 & x < 2
honest: {if x = 1 -> a; if x = 2}

A
  honest go -> B: 1, A: -x  # a < b
  stop -> ? reveals x
    if low: x < 1 -> B
`;

const RULES = `players: Ann, Bob
constants: coin
state: round = 1

honest move pass by Ann, Bob  # lets the pile grow
  if round < 6 and not done
  set round = round + 1
  pay me: coin, Bob: 2 * coin
  next other
`;

test('the highlighted text is the text, with a newline at the end', () => {
    assert.equal(unhighlight(highlightCompact(COMPACT, 0)), COMPACT + '\n');
    assert.equal(unhighlight(highlightRules(RULES, 0)), RULES + '\n');
});

test('the compact format', () => {
    const html = highlightCompact(COMPACT, 0);
    assert.deepEqual(classes(html, 'players'), ['h-key']);
    assert.deepEqual(classes(html, 'honest'), ['h-key', 'h-key']);
    assert.deepEqual(classes(html, 'go'), ['h-action']);
    assert.deepEqual(classes(html, '0'), ['h-num']);
    assert.ok(classes(html, 'B').includes('h-player'));
    assert.deepEqual(classes(html, '# a &lt; b'), ['h-comment']);
    assert.deepEqual(classes(html, 'reveals'), ['h-key']);
    assert.deepEqual(classes(html, 'low'), ['h-action']);
});

test('rules', () => {
    const html = highlightRules(RULES, 0);
    for (const word of ['move', 'by', 'if', 'set', 'pay', 'next', 'and', 'not', 'me', 'other'])
        assert.ok(classes(html, word).includes('h-key'), word);
    assert.deepEqual(classes(html, 'pass'), ['h-action']);
    assert.ok(classes(html, 'Bob').every(c => c === 'h-player'));
    assert.deepEqual(classes(html, 'coin'), ['h-const', 'h-const', 'h-const']);
    assert.deepEqual(classes(html, '6'), ['h-num']);
});

test('the line of an error is marked', () => {
    for (const [highlighter, text] of [[highlightCompact, COMPACT], [highlightRules, RULES]] as const) {
        const lines = highlighter(text, 2).split('\n');
        assert.ok(lines[1].startsWith('<span class="h-error">'));
        assert.ok(!lines[0].includes('h-error') && !lines[2].includes('h-error'));
        // an empty line is marked too
        assert.ok(highlighter('a\n\nb', 2).split('\n')[1].includes('h-error'));
    }
});
