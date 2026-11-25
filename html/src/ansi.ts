// Terminal colours (ANSI SGR escape sequences, as checkmate --color=always writes them) as HTML: spans with the
// classes a-bold, a-dim and a-fg0 to a-fg15, for the page's style sheet to colour. Other escape sequences are dropped.

import { escapeHtml } from './text.ts';

interface Style { bold: boolean; dim: boolean; fg: number | null }

function classes(style: Style) {
    return [style.bold ? 'a-bold' : '', style.dim ? 'a-dim' : '', style.fg === null ? '' : 'a-fg' + style.fg].filter(c => c).join(' ');
}

function apply(style: Style, params: string): Style {
    const s = { ...style };
    for (const p of params === '' ? [0] : params.split(';').map(Number)) {
        if (p === 0) { s.bold = false; s.dim = false; s.fg = null; }
        else if (p === 1) s.bold = true;
        else if (p === 2) s.dim = true;
        else if (p === 22) { s.bold = false; s.dim = false; }
        else if (p >= 30 && p <= 37) s.fg = p - 30;
        else if (p >= 90 && p <= 97) s.fg = p - 90 + 8;
        else if (p === 39) s.fg = null;
    }
    return s;
}

export function ansiToHtml(text: string): string {
    let style: Style = { bold: false, dim: false, fg: null }, html = '', last = 0;
    const emit = (part: string) => {
        if (!part) return;
        const cls = classes(style);
        html += cls ? `<span class="${cls}">${escapeHtml(part)}</span>` : escapeHtml(part);
    };
    for (const m of text.matchAll(/\x1b\[([0-9;]*)([A-Za-z])/g)) {
        emit(text.slice(last, m.index));
        if (m[2] === 'm') style = apply(style, m[1]);
        last = m.index! + m[0].length;
    }
    emit(text.slice(last));
    return html;
}
