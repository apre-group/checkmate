// Syntax highlighting for the compact game format: returns HTML for the <pre> behind the editor.

export function highlightCompact(text: string, errorLine: number): string {
    const esc = (s: string) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    const span = (cls: string, s: string) => s ? `<span class="${cls}">${esc(s)}</span>` : '';
    const names = (s: string, cls: string) => s.split(/(\s*,\s*|\s+)/).map(p => /^[\s,]*$/.test(p) ? esc(p) : span(cls, p)).join('');
    const expression = (s: string) => s.split(/(\d+(?:\.\d+)?|[A-Za-z_]\w*)/).map((p, i) =>
        i % 2 ? span(/^\d/.test(p) ? 'h-num' : 'h-const', p) : esc(p)).join('');
    const utilities = (s: string) => s.split(/(,)/).map(part => {
        if (part === ',') return ',';
        const m = part.match(/^(\s*)([^:]+?)(\s*:\s*)(.*)$/);
        return m ? esc(m[1]) + span('h-player', m[2]) + esc(m[3]) + expression(m[4]) : esc(part);
    }).join('');
    // CEFGs: {if CONDITION -> rest; ...} in honest histories and utilities, with `rest` highlighted by `inner`
    const conditional = (s: string, inner: (s: string) => string) => {
        let afterIf = false;
        return s.split(/(\{|\}|;|->|\bif\b)/).map(p => {
            if (p === 'if') { afterIf = true; return span('h-key', p); }
            if (p === '->' || p === ';' || p === '}') { afterIf = false; return span('h-arrow', p); }
            if (p === '{') return span('h-arrow', p);
            return afterIf ? expression(p) : inner(p);
        }).join('');
    };
    // a node with lines below it: a player, or ? [reveals CONSTANT, ...] for a condition node
    const head = (s: string) => {
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
                html = esc(code.match(/^\s*/)![0]) + head(code.trim());  // the root
            } else {
                const [, indent, action, arrow, rest] = m;
                // below a condition node: if [NAME:] CONDITION
                const c = action.match(/^if(\s+)(?:([^\s:]+)(\s*:\s*))?(.*)$/);
                const marked = action.match(/^honest(\s+)(.*)$/);
                html = esc(indent) + (c ? span('h-key', 'if') + esc(c[1]) + span('h-action', c[2] || '') + esc(c[3] || '') +
                                          expression(c[4])
                                        : marked ? span('h-key', 'honest') + esc(marked[1]) + span('h-action', marked[2])
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

// Syntax highlighting for rules (see html/src/rules.ts).
export function highlightRules(text: string, errorLine: number): string {
    const esc = (s: string) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    const span = (cls: string, s: string) => s ? `<span class="${cls}">${esc(s)}</span>` : '';
    const players = new Set<string>();
    for (const m of text.matchAll(/^players\s*:([^#\n]*)/gm)) m[1].split(',').forEach(p => players.add(p.trim()));
    const WORDS = new Set(['and', 'or', 'not', 'me', 'other', 'yes', 'no', 'true', 'false']);
    const expression = (s: string) => s.split(/(\d+(?:\.\d+)?|[A-Za-z_]\w*)/).map((p, i) =>
        i % 2 === 0 ? esc(p) : /^\d/.test(p) ? span('h-num', p) : WORDS.has(p) ? span('h-key', p)
            : players.has(p) ? span('h-player', p) : span('h-const', p)).join('');
    const lines = text.split('\n').map((line, k) => {
        const hash = line.indexOf('#');
        const code = hash < 0 ? line : line.slice(0, hash), comment = hash < 0 ? '' : line.slice(hash);
        let html;
        const move = code.match(/^(honest\s+)?(move)(\s+)(\S*)(\s+)(by)(.*)$/);
        const clause = code.match(/^(\s+)(if|set|pay|next|end)\b(.*)$/);
        const header = code.match(/^([A-Za-z_]+)(\s*:\s*)(.*)$/);
        if (move) {
            const [, honest = '', word, s1, name, s2, by, rest] = move;
            html = span('h-key', honest.trim()) + esc(honest.slice(honest.trimEnd().length)) + span('h-key', word) + esc(s1) +
                span('h-action', name) + esc(s2) + span('h-key', by) + expression(rest);
        } else if (clause) {
            html = esc(clause[1]) + span('h-key', clause[2]) + expression(clause[3]);
        } else if (header) {
            const [, key, sep, value] = header;
            html = span('h-key', key) + esc(sep) + expression(value);
        } else {
            html = esc(code);
        }
        html += span('h-comment', comment);
        return k + 1 === errorLine ? `<span class="h-error">${html || ' '}</span>` : html;
    });
    return lines.join('\n') + '\n';
}
