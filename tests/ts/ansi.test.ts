import { test } from 'node:test';
import assert from 'node:assert/strict';
import { ansiToHtml } from '../../html/src/ansi.ts';

test('plain text is escaped and nothing else', () => {
    assert.equal(ansiToHtml('a < b & c'), 'a &lt; b &amp; c');
    assert.equal(ansiToHtml(''), '');
});

test('colours, bold and dim, until a reset', () => {
    assert.equal(ansiToHtml('  weak immunity: \x1b[1;32mYES\x1b[0m'), '  weak immunity: <span class="a-bold a-fg2">YES</span>');
    assert.equal(ansiToHtml('\x1b[31mred\x1b[39m plain'), '<span class="a-fg1">red</span> plain');
    assert.equal(ansiToHtml('\x1b[2mdim\x1b[22m'), '<span class="a-dim">dim</span>');
    assert.equal(ansiToHtml('\x1b[95mbright'), '<span class="a-fg13">bright</span>');
    assert.equal(ansiToHtml('\x1b[1mbold\x1b[mplain'), '<span class="a-bold">bold</span>plain');
});

test('styles combine and change across lines', () => {
    assert.equal(ansiToHtml('\x1b[1mHonest history:\x1b[0m \x1b[35mq\x1b[0m\n  x'),
        '<span class="a-bold">Honest history:</span> <span class="a-fg5">q</span>\n  x');
    assert.equal(ansiToHtml('\x1b[1m\x1b[36mboth\x1b[0m'), '<span class="a-bold a-fg6">both</span>');
});

test('other escape sequences and unknown codes are dropped', () => {
    assert.equal(ansiToHtml('a\x1b[2Kb\x1b[4mc'), 'abc');
    assert.equal(ansiToHtml('\x1b[31m<x>\x1b[0m'), '<span class="a-fg1">&lt;x&gt;</span>');
});
