// Syntax highlighting for the compact game format: returns HTML for the <pre> behind the editor.

function highlightCompact(text, errorLine) {
    const esc = s => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    const span = (cls, s) => s ? `<span class="${cls}">${esc(s)}</span>` : '';
    const names = (s, cls) => s.split(/(\s*,\s*|\s+)/).map(p => /^[\s,]*$/.test(p) ? esc(p) : span(cls, p)).join('');
    const expression = s => s.split(/(\d+(?:\.\d+)?|[A-Za-z_]\w*)/).map((p, i) =>
        i % 2 ? span(/^\d/.test(p) ? 'h-num' : 'h-const', p) : esc(p)).join('');
    const utilities = s => s.split(/(,)/).map(part => {
        if (part === ',') return ',';
        const m = part.match(/^(\s*)([^:]+?)(\s*:\s*)(.*)$/);
        return m ? esc(m[1]) + span('h-player', m[2]) + esc(m[3]) + expression(m[4]) : esc(part);
    }).join('');
    // CEFGs: {if CONDITION -> rest; ...} in honest histories and utilities, with `rest` highlighted by `inner`
    const conditional = (s, inner) => {
        let afterIf = false;
        return s.split(/(\{|\}|;|->|\bif\b)/).map(p => {
            if (p === 'if') { afterIf = true; return span('h-key', p); }
            if (p === '->' || p === ';' || p === '}') { afterIf = false; return span('h-arrow', p); }
            if (p === '{') return span('h-arrow', p);
            return afterIf ? expression(p) : inner(p);
        }).join('');
    };
    // a node with lines below it: a player, or ? [reveals CONSTANT, ...] for a condition node
    const head = s => {
        const m = s.match(/^\?(\s*)(reveals\b)?(.*)$/);
        return m ? span('h-key', '?') + esc(m[1]) + span('h-key', m[2] || '') + names(m[3], 'h-const') : span('h-player', s);
    };
    const NAME_KEYS = ['players', 'constants', 'infinitesimals', 'unknown_constants', 'unknown_infinitesimals'];
    let inTree = false;

    const lines = text.split('\n').map((line, k) => {
        const hash = line.indexOf('#');
        const code = hash < 0 ? line : line.slice(0, hash);
        const comment = hash < 0 ? '' : line.slice(hash);
        let html;
        // (the value of a conditional honest history or utility has -> in it)
        const header = !inTree && code.match(/^([A-Za-z_]+)(\s*:\s*)(.*)$/);
        if (!code.trim()) {
            html = esc(code);
        } else if (header) {
            const [, key, sep, value] = header;
            html = span('h-key', key) + esc(sep) + (
                NAME_KEYS.includes(key) ? names(value, key === 'players' ? 'h-player' : 'h-const') :
                key === 'honest' ? conditional(value, p => names(p, 'h-action')) :
                key === 'honest_utility' ? conditional(value, utilities) : expression(value));
        } else {
            inTree = true;
            const m = code.match(/^(\s*)(.*?)(\s*->\s*)(.*)$/);
            if (!m) {
                html = esc(code.match(/^\s*/)[0]) + head(code.trim());  // the root
            } else {
                const [, indent, action, arrow, rest] = m;
                // below a condition node: if [NAME:] CONDITION
                const c = action.match(/^if(\s+)(?:([^\s:]+)(\s*:\s*))?(.*)$/);
                html = esc(indent) + (c ? span('h-key', 'if') + esc(c[1]) + span('h-action', c[2] || '') + esc(c[3] || '') +
                                          expression(c[4])
                                        : span('h-action', action)) + span('h-arrow', arrow) + (
                    rest.startsWith('subtree') ? span('h-subtree', rest) :
                    rest.includes(':') ? utilities(rest) : head(rest));
            }
        }
        html += span('h-comment', comment);
        return k + 1 === errorLine ? `<span class="h-error">${html || ' '}</span>` : html;
    });
    // a trailing newline needs a line of its own, or the backdrop ends up one line short
    return lines.join('\n') + '\n';
}
