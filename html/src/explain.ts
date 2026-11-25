// The results in words: what a property means, the verdict, and the selected strategy or counterexample.

import type { Counterexample, Game, HistoryElement, Result, Strategy, TreeNode } from './game.ts';
import { NAMES, caseText, escapeHtml, historyText } from './text.ts';

// a line below the results: a case, or a strategy or counterexample to show in the tree
export interface Item {
    label?: string;
    r: Result;
    kind: 'case' | 'strategy' | 'ce';
    s?: Strategy;
    ce?: Counterexample;
}

const MEANING: Record<string, string> = {
    weak_immunity: 'A player who plays honestly never ends up with a negative payoff, whatever the other players do.',
    weaker_immunity: 'As weak immunity, except that infinitesimals do not count: a payoff only has to be non-negative apart from them.',
    collusion_resilience: 'No group of players (short of all of them) gets more in total by deviating from the honest history together.',
    practicality: 'Playing honestly is what rational players do: at every point, the honest action is a best choice, given that ' +
        'everyone plays rationally from then on (the honest history is a subgame perfect equilibrium).',
};

const code = (s: string) => `<code>${escapeHtml(s)}</code>`;
const who = (ps: string[]) => ps.length <= 1 ? (ps[0] || 'no player') : ps.slice(0, -1).join(', ') + ' and ' + ps[ps.length - 1];
const after = (h: string[]) => h.length ? 'after ' + code(historyText(h)) : 'at the start';
const oneOf = (as: string[]) => as.length === 1 ? code(as[0]) : 'one of ' + as.map(code).join(', ');
const inCase = (c: string[]) => c.length ? ` when ${code(caseText(c))}` : '';
const list = (vs: string[]) => vs.length === 1 ? code(vs[0]) : vs.slice(0, -1).map(code).join(', ') + ' and ' + code(vs[vs.length - 1]);

// the node at the end of `path`, or null if it leaves the tree (or passes a condition node)
function nodeAt(game: Game, path: HistoryElement[]): TreeNode | null {
    let node = game.tree;
    for (const a of path) {
        const c = typeof a === 'string' ? (node.children || []).find(c => c.action === a) : undefined;
        if (!c) return null;
        node = c.child;
    }
    return node;
}

function payoff(game: Game, path: HistoryElement[] | undefined, player: string): string | null {
    const u = path && nodeAt(game, path)?.utility?.find(u => u.player === player);
    return u ? String(u.value) : null;
}

// ", where Bob gets x instead of y on the honest history", from the leaf at `path`
function gets(game: Game, path: string[], players: string[], r: Result) {
    const there = players.map(p => payoff(game, path, p)), honest = players.map(p => payoff(game, r.history, p));
    if (there.some(v => v === null)) return '';
    return `, where ${escapeHtml(who(players))} ${players.length === 1 ? 'gets' : 'get'} ${list(there as string[])}` +
        (honest.some(v => v === null) ? '' : ` instead of ${list(honest as string[])} on the honest history`);
}

function strategyText(r: Result, s: Strategy) {
    const MAX = 12;
    return `<p>A strategy that shows it${inCase(s.case)} (green in the tree):</p><ul>` +
        s.strategy.slice(0, MAX).map(e => `<li>${escapeHtml(e.player)} plays ${code(e.action)} ${after(e.history)}</li>`).join('') +
        (s.strategy.length > MAX ? `<li>and ${s.strategy.length - MAX} more moves</li>` : '') + '</ul>' +
        (r.property.endsWith('immunity') ? '<p>The other actions can be anything.</p>' : '');
}

function counterexampleText(game: Game, r: Result, ce: Counterexample) {
    const prop = r.property;
    if (prop === 'weak_immunity' || prop === 'weaker_immunity')
        return `<p>${escapeHtml(who(ce.player_group))} can end up with a negative payoff` +
            (prop === 'weaker_immunity' ? ' (apart from infinitesimals)' : '') +
            ` while playing honestly${inCase(ce.case)}, if (red in the tree):</p><ul>` +
            ce.choices.map(c => `<li>${escapeHtml(c.player)} plays ${oneOf(c.actions)} ${after(c.history)}</li>`).join('') + '</ul>';
    if (prop === 'collusion_resilience') {
        const leaves = (ce.cr_leaves || []).map(l => `<li>The game then ends at ${code(historyText(l.history))}` +
            (l.subtree ? `, in a subtree, where ${escapeHtml(l.groups.map(who).join(' or '))} get more`
                       : gets(game, l.history, [...new Set(l.groups.flat())], r)) + '.</li>');
        return `<p>Deviating from the honest history pays off${inCase(ce.case)} (red in the tree):</p><ul>` +
            ce.choices.map(c => `<li>${escapeHtml(c.player)} deviates to ${oneOf(c.actions)} ${after(c.history)}</li>`).join('') +
            leaves.join('') + (ce.cr_more_omitted ? '<li>and more</li>' : '') + '</ul>';
    }
    if (prop === 'practicality') {
        // the history of a choice ends with the deviating action; its actions are how rational play continues
        const p = ce.player_group[0], first = ce.choices[0];
        if (!p || !first || !first.history.length) return '';
        const at = first.history.slice(0, -1), mover = nodeAt(game, at)?.player || 'a player';
        const deviation = `${code(first.history[first.history.length - 1])} ${after(at)}`;
        return `<p>${escapeHtml(p)} is better off ` +
            (mover === p ? `playing ${deviation}` : `if ${escapeHtml(mover)} plays ${deviation}`) +
            ` instead of following the honest history${inCase(ce.case)}. With everyone playing rationally from ` +
            `there (red in the tree), the game goes:</p><ul>` +
            ce.choices.map(c => {
                const path = c.history.concat(c.actions);
                return `<li>${code(historyText(path))}${gets(game, path, [p], r)}</li>`;
            }).join('') + '</ul>';
    }
    return '';
}

export function explain(game: Game, it: Item): string {
    const r = it.r, history = r.history ? code(historyText(r.history) || '(empty)') : 'this run';
    const name = NAMES[r.property] || r.property;
    let verdict;
    if (r.holds === null) verdict = `CheckMate could not decide this for ${history}` + (r.undecided ? ': ' + escapeHtml(r.undecided) : '.');
    else if (r.holds) verdict = `<b>Yes</b>, for the honest history ${history}` + ((r.cases || []).length > 1 ? ', in every case below.' : '.');
    else verdict = `<b>No</b>, not for the honest history ${history}` +
        ((r.cases || []).some(c => c.holds) ? ': it holds in some of the cases below, but not in all.' : '.');
    return `<p><b>${name[0].toUpperCase() + name.slice(1)}:</b> ${MEANING[r.property] || ''}</p><p>${verdict}</p>` +
        (it.kind === 'strategy' && it.s ? strategyText(r, it.s) : '') +
        (it.kind === 'ce' && it.ce ? counterexampleText(game, r, it.ce) : '') +
        (r.precondition ? `<p>It holds exactly when ${code(r.precondition)} (the weakest precondition).</p>` : '');
}
