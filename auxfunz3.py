# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Optional, Union, Set, Generator, Tuple
from fractions import Fraction
import z3

Real = Union[float, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
LabelFn = Optional[Callable[[Real, Real, bool], z3.BoolRef]]


def negation(to_negate: Boolean) -> z3.BoolRef:
    """negate a Z3 expression while satisfying the type checker"""
    negated = z3.Not(to_negate)
    assert isinstance(negated, z3.BoolRef)
    return negated


def disjunction(*disjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 disjunction while satisfying the type checker"""
    result = z3.Or(disjuncts)
    assert isinstance(result, z3.BoolRef)
    return result


def conjunction(*conjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 conjunction while satisfying the type checker"""
    result = z3.And(conjuncts)
    assert isinstance(result, z3.BoolRef)
    return result


def implication(left: Boolean, right: Boolean) -> z3.BoolRef:
    """build a Z3 implication while satisfying the type checker"""
    return z3.Implies(left, right)


def simplify_boolean(expr: z3.BoolRef) -> z3.BoolRef:
    """simplify the Boolean `expr` while satisfying the type checker"""
    simplified = z3.simplify(expr)
    assert isinstance(simplified, z3.BoolRef)
    return simplified


def label(
        left: Real,
        right: Real,
        op: Callable[[Real, Real], Boolean],
        label_fn: LabelFn,
        real: bool
) -> Boolean:
    """
    build the expression `(label => op(left, right))`

    `label_fn(left, right, real)` is called to supply `label`
    """
    comparison = op(left, right)
    if label_fn is None:
        return comparison
    label_expr = label_fn(left, right, real)
    return implication(label_expr, comparison)


def evaluate_model(model: z3.ModelRef, left: Real, right: Real) -> z3.BoolRef:
    """compute comparative constraint based on given model"""
    if model.evaluate(left > right, True):
        return left > right
    elif model.evaluate(left == right, True):
        return left == right
    else:
        return right > left


def order_according_to_model(model: z3.ModelRef, minimize: z3.Solver, terms: Set[Tuple[Real, Real]]) -> Set[Boolean]:
    """
    compute the order of terms according to the model and return it as a set of constraints
    (also exclude those that can be shown by `minimize`)
    """

    def valuation(term: Real) -> Fraction:
        if not isinstance(term, z3.ArithRef):
            return Fraction(term)

        value = model.evaluate(term, model_completion=True)
        assert isinstance(value, z3.RatNumRef) or isinstance(value, z3.IntNumRef)
        value = value.as_fraction() if isinstance(value, z3.RatNumRef) else Fraction(value.as_long())
        return value

    def split(left: Real, right: Real) -> Boolean:
        left_val = valuation(left)
        right_val = valuation(right)
        if left_val > right_val:
            return left > right
        elif left_val == right_val:
            return left == right
        else:
            return left < right

    comparisons = {
        split(left, right)
        for left, right in terms
    }

    redundant = set()
    for comparison in comparisons:
        if minimize.check(*(comparisons - redundant - {comparison}), negation(comparison)) == z3.unsat:
            redundant.add(comparison)

    return comparisons - redundant


def minimize_unsat_core(solver: z3.Solver, core: Set[z3.BoolRef], *assumptions: z3.BoolRef) -> Set[z3.BoolRef]:
    """
    minimize `core` with respect to `solver` under `assumptions`
    only necessary because Z3's version is a bit rubbish under our loads for some reason
    """
    remove = set()
    for label in core:
        if solver.check(*(core - remove - {label}), *assumptions) == z3.unsat:
            remove.add(label)

    return core - remove

# following functions adapted from "Programming Z3"
def maximal_satisfying_subset(solver: z3.Solver, start: Set[z3.BoolRef], all: Set[z3.BoolRef], *assumptions: z3.BoolRef) -> Set[z3.BoolRef]:
    """compute a maximal satisfying subset of `all`, starting from `start` with respect to `solver` + `assumptions`"""
    ps = all - start
    mss = start
    backbones = set()
    while len(ps) > 0:
        p = ps.pop()
        if solver.check(*(mss | backbones | { p }), *assumptions) == z3.sat:
            model = solver.model()
            mss = mss | { p } | {
                q for q in ps
                if z3.is_true(model.eval(q))
            }
            ps = ps - mss
        else:
            backbones = backbones | { negation(p) }

    return mss

def minimal_unsat_cores(solver: z3.Solver, all: Set[z3.BoolRef], *assumptions: z3.BoolRef) -> Generator[Set[z3.BoolRef], None, None]:
    """iteratively compute all minimal unsat cores in `all` with respect to `solver` + `assumptions`"""

    map = z3.Solver()
    map.set("unsat_core", True)
    map.set("core.minimize", True)
    while map.check() == z3.sat:
        model = map.model()
        seed = {
            p for p in all
            if not z3.is_false(model.eval(p))
        }
        if solver.check(*seed, *assumptions) == z3.sat:
            mss = maximal_satisfying_subset(solver, seed, all, *assumptions)
            map.add(disjunction(*(all - mss)))
        else:
            mus = {
                label
                for label in solver.unsat_core()
                if isinstance(label, z3.BoolRef) and label in all
            }
            map.add(disjunction(*(negation(label) for label in mus)))
            yield mus
