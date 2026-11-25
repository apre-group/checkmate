import type { HistoryElement } from './game.ts';

export const NAMES: Record<string, string> = { weak_immunity: 'weak immunity', weaker_immunity: 'weaker immunity',
    collusion_resilience: 'collusion resilience', practicality: 'practicality' };

export function escapeHtml(s: unknown) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }

export function caseText(c: string[]) { return c.length ? c.join(' ∧ ') : '(any)'; }

// in CEFGs, an element of a history can be a list of conditions, each with the history that continues under it,
// written as in the compact format: {if CONDITION → history; ...}
export function historyText(h: HistoryElement[]): string {
    return h.map(a => typeof a === 'string' ? a
        : '{' + a.map(c => 'if ' + c.condition + (c.path.length ? ' → ' + historyText(c.path) : '')).join('; ') + '}').join(' → ');
}
