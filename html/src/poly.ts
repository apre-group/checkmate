// Payoffs as polynomials over constants and infinitesimals with exact rational coefficients, so that the payoffs
// collected along a play add up to one simplified expression.

export class Rational {
    readonly n: bigint;
    readonly d: bigint;
    constructor(n: bigint, d: bigint = 1n) {
        if (d === 0n) throw new Error('division by zero');
        if (d < 0n) { n = -n; d = -d; }
        const g = gcd(n < 0n ? -n : n, d);
        this.n = n / g;
        this.d = d / g;
    }
    static parse(text: string): Rational {
        const [whole, frac = ''] = text.split('.');
        return new Rational(BigInt(whole + frac), 10n ** BigInt(frac.length));
    }
    add(o: Rational) { return new Rational(this.n * o.d + o.n * this.d, this.d * o.d); }
    mul(o: Rational) { return new Rational(this.n * o.n, this.d * o.d); }
    div(o: Rational) { return new Rational(this.n * o.d, this.d * o.n); }
    neg() { return new Rational(-this.n, this.d); }
    isZero() { return this.n === 0n; }
    isOne() { return this.n === 1n && this.d === 1n; }
    // CheckMate reads decimals but not fractions: null if this has no finite decimal expansion
    decimal(): string | null {
        let d = this.d, twos = 0, fives = 0;
        while (d % 2n === 0n) { d /= 2n; twos++; }
        while (d % 5n === 0n) { d /= 5n; fives++; }
        if (d !== 1n) return null;
        const digits = Math.max(twos, fives), scaled = this.n * 10n ** BigInt(digits) / this.d;
        const abs = (scaled < 0n ? -scaled : scaled).toString().padStart(digits + 1, '0');
        const text = digits ? abs.slice(0, -digits) + '.' + abs.slice(-digits) : abs;
        return (scaled < 0n ? '-' : '') + text;
    }
}

function gcd(a: bigint, b: bigint): bigint {
    while (b) [a, b] = [b, a % b];
    return a || 1n;
}

// a sum of terms, each a coefficient times a product of symbols (the key: the symbols sorted, joined by *)
export class Poly {
    readonly terms: Map<string, Rational>;
    constructor(terms: Map<string, Rational> = new Map()) { this.terms = terms; }
    static constant(r: Rational) { return new Poly(r.isZero() ? new Map() : new Map([['', r]])); }
    static symbol(name: string) { return new Poly(new Map([[name, new Rational(1n)]])); }

    add(o: Poly): Poly {
        const terms = new Map(this.terms);
        for (const [k, c] of o.terms) {
            const sum = (terms.get(k) || new Rational(0n)).add(c);
            if (sum.isZero()) terms.delete(k);
            else terms.set(k, sum);
        }
        return new Poly(terms);
    }
    neg(): Poly { return new Poly(new Map([...this.terms].map(([k, c]) => [k, c.neg()]))); }
    mul(o: Poly): Poly {
        let result = new Poly();
        for (const [k1, c1] of this.terms)
            for (const [k2, c2] of o.terms) {
                const key = [...(k1 ? k1.split('*') : []), ...(k2 ? k2.split('*') : [])].sort().join('*');
                result = result.add(new Poly(new Map([[key, c1.mul(c2)]])));
            }
        return result;
    }
    // the constant this is, or null if it has symbols
    asConstant(): Rational | null {
        if (this.terms.size === 0) return new Rational(0n);
        return this.terms.size === 1 && this.terms.has('') ? this.terms.get('')! : null;
    }

    // e.g. "closed - wait + 2 * fee"; throws if a coefficient has no finite decimal expansion
    toString(): string {
        if (this.terms.size === 0) return '0';
        let text = '';
        for (const [key, c] of this.terms) {
            const negative = c.n < 0n, abs = negative ? c.neg() : c;
            const number = abs.decimal();
            if (number === null) throw new Error(`the payoff has the coefficient ${c.n}/${c.d}, which has no finite decimal expansion (CheckMate needs decimals)`);
            const factors = key ? key.split('*') : [];
            const term = [...(abs.isOne() && factors.length ? [] : [number]), ...factors].join(' * ');
            text += !text ? (negative ? '-' : '') + term : (negative ? ' - ' : ' + ') + term;
        }
        return text;
    }
}
