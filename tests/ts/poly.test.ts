import { test } from 'node:test';
import assert from 'node:assert/strict';
import { Poly, Rational } from '../../html/src/poly.ts';

const r = (text: string) => Rational.parse(text);
const x = Poly.symbol('x'), y = Poly.symbol('y'), e = Poly.symbol('e');
const c = (text: string) => Poly.constant(r(text));

test('rationals are exact and reduced', () => {
    assert.equal(r('0.1').add(r('0.2')).decimal(), '0.3');
    assert.equal(r('0.50').decimal(), '0.5');
    assert.equal(r('10').decimal(), '10');
    assert.equal(r('0').decimal(), '0');
    const third = new Rational(1n, 3n);
    assert.equal(third.n, 1n);
    assert.equal(new Rational(2n, -6n).n, -1n);
    assert.equal(new Rational(2n, -6n).d, 3n);
    assert.ok(new Rational(0n, 5n).isZero());
    assert.ok(new Rational(4n, 4n).isOne());
});

test('decimals of fractions with only 2 and 5 in the denominator', () => {
    assert.equal(new Rational(1n, 4n).decimal(), '0.25');
    assert.equal(new Rational(-1n, 8n).decimal(), '-0.125');
    assert.equal(new Rational(-1n, 2n).decimal(), '-0.5');
    assert.equal(new Rational(7n, 20n).decimal(), '0.35');
    assert.equal(new Rational(123n, 10n).decimal(), '12.3');
    assert.equal(new Rational(1n, 3n).decimal(), null);
    assert.equal(new Rational(1n, 6n).decimal(), null);
});

test('division by zero throws', () => {
    assert.throws(() => new Rational(1n, 0n));
    assert.throws(() => r('1').div(r('0')));
});

test('polynomials add up and cancel', () => {
    assert.equal(new Poly().toString(), '0');
    assert.equal(x.add(y.neg()).toString(), 'x - y');
    assert.equal(x.add(x.neg()).toString(), '0');
    assert.equal(x.add(x).toString(), '2 * x');
    assert.equal(x.neg().toString(), '-x');
    assert.equal(c('0.1').add(c('0.2')).add(x).toString(), '0.3 + x');
    assert.equal(c('-3').add(x).toString(), '-3 + x');
    assert.equal(x.add(c('-3')).toString(), 'x - 3');
});

test('terms keep the order in which they first appear', () => {
    assert.equal(e.add(x).add(y).toString(), 'e + x + y');
    assert.equal(y.add(x).add(e).toString(), 'y + x + e');
    // a term that cancels and comes back goes to the end
    assert.equal(x.add(y).add(x.neg()).add(x).toString(), 'y + x');
});

test('products of symbols', () => {
    assert.equal(x.mul(x).toString(), 'x * x');
    assert.equal(x.mul(y).add(y.mul(x)).toString(), '2 * x * y');
    assert.equal(x.add(c('1')).mul(x.add(c('-1'))).toString(), 'x * x - 1');
    assert.equal(c('0.5').mul(x).toString(), '0.5 * x');
    assert.equal(c('0').mul(x).toString(), '0');
});

test('constants', () => {
    assert.equal(c('2.5').asConstant()!.decimal(), '2.5');
    assert.equal(new Poly().asConstant()!.decimal(), '0');
    assert.equal(x.asConstant(), null);
    assert.equal(x.add(c('1')).asConstant(), null);
});

test('a coefficient without a finite decimal cannot be printed', () => {
    assert.throws(() => Poly.constant(new Rational(1n, 3n)).mul(x).toString(), /1\/3/);
});
