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
    const NAME_KEYS = ['players', 'constants', 'infinitesimals'];
    let inTree = false;

    const lines = text.split('\n').map((line, k) => {
        const hash = line.indexOf('#');
        const code = hash < 0 ? line : line.slice(0, hash);
        const comment = hash < 0 ? '' : line.slice(hash);
        let html;
        const header = !inTree && code.match(/^([A-Za-z_]+)(\s*:\s*)(.*)$/);
        if (!code.trim()) {
            html = esc(code);
        } else if (header && !code.includes('->')) {
            const [, key, sep, value] = header;
            html = span('h-key', key) + esc(sep) + (
                NAME_KEYS.includes(key) ? names(value, key === 'players' ? 'h-player' : 'h-const') :
                key === 'honest' ? names(value, 'h-action') :
                key === 'honest_utility' ? utilities(value) : expression(value));
        } else {
            inTree = true;
            const m = code.match(/^(\s*)(.*?)(\s*->\s*)(.*)$/);
            if (!m) {
                html = esc(code.match(/^\s*/)[0]) + span('h-player', code.trim());  // the root
            } else {
                const [, indent, action, arrow, rest] = m;
                html = esc(indent) + span('h-action', action) + span('h-arrow', arrow) + (
                    rest.startsWith('subtree') ? span('h-subtree', rest) :
                    rest.includes(':') ? utilities(rest) : span('h-player', rest));
            }
        }
        html += span('h-comment', comment);
        return k + 1 === errorLine ? `<span class="h-error">${html || ' '}</span>` : html;
    });
    // a trailing newline needs a line of its own, or the backdrop ends up one line short
    return lines.join('\n') + '\n';
}
