import { test } from 'node:test';
import assert from 'node:assert/strict';
import { caseText, escapeHtml, historyText } from '../../html/src/text.ts';

test('histories, also through condition nodes', () => {
    assert.equal(historyText([]), '');
    assert.equal(historyText(['a', 'b']), 'a → b');
    assert.equal(historyText(['dev', 'risk', [{ condition: 'y = 0', path: ['l'] }, { condition: 'y = 1', path: [] }]]),
        'dev → risk → {if y = 0 → l; if y = 1}');
});

test('cases', () => {
    assert.equal(caseText([]), '(any)');
    assert.equal(caseText(['a > 0', 'b < a']), 'a > 0 ∧ b < a');
});

test('escaping', () => {
    assert.equal(escapeHtml('<a & b>'), '&lt;a &amp; b&gt;');
    assert.equal(escapeHtml(3), '3');
});
