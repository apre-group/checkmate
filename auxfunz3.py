# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Optional, Union, Set, Generator
import z3

Real = Union[float, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
LabelFn = Optional[Callable[[Real, Real, bool], z3.BoolRef]]


def negation(negated: Boolean) -> z3.BoolRef:
    """negate a Z3 expression while satisfying the typechecker"""
    negation = z3.Not(negated)
    assert isinstance(negation, z3.BoolRef)
    return negation


def disjunction(*disjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 disjuncts while satisfying the typechecker"""
    disjunction = z3.Or(disjuncts)
    assert isinstance(disjunction, z3.BoolRef)
    return disjunction


def conjunction(*conjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 conjunction while satisfying the typechecker"""
    conjunction = z3.And(conjuncts)
    assert isinstance(conjunction, z3.BoolRef)
    return conjunction


def implication(left: Boolean, right: Boolean) -> z3.BoolRef:
    """build a Z3 implication while satisfying the typechecker"""
    return z3.Implies(left, right)


def simplify_boolean(expr: z3.BoolRef) -> z3.BoolRef:
    """simplify the Boolean `expr` while satisfying the typechecker"""
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
    label = label_fn(left, right, real)
    return implication(label, comparison)


def eliminate_consequences(solver: z3.Solver, constraints: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    """compute a greedy consequence elimination of `constraints` wrt `solver`"""
    to_elim = set()
    for constr in constraints:
        to_check = constraints - to_elim - {constr} | {negation(constr)}
        if solver.check(*to_check) == z3.unsat:
            to_elim.add(constr)
    return constraints - to_elim


# following functions adapted from "Programming Z3"
def maximal_satisfying_subset(solver: z3.Solver, start: Set[z3.BoolRef], all: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    """compute a maximal satisfying subset of `all`, starting from `start` with respect to `solver`"""
    ps = all - start
    mss = start
    backbones = set()
    while len(ps) > 0:
        p = ps.pop()
        if solver.check(*(mss | backbones | { p })) == z3.sat:
            model = solver.model()
            mss = mss | { p } | {
                q for q in ps
                if z3.is_true(model.eval(q))
            }
            ps = ps - mss
        else:
            backbones = backbones | { negation(p) }

    return mss

def minimal_unsat_cores(solver: z3.Solver, all: Set[z3.BoolRef]) -> Generator[Set[z3.BoolRef], None, None]:
    """iteratively compute all minimal unsat cores in `all` with respect to `solver`"""

    map = z3.Solver()
    map.set("unsat_core", True)
    map.set("core.minimize", True)
    while map.check() == z3.sat:
        model = map.model()
        seed = {
            p for p in all
            if not z3.is_false(model.eval(p))
        }
        if solver.check(*seed) == z3.sat:
            mss = maximal_satisfying_subset(solver, seed, all)
            map.add(disjunction(*(all - mss)))
        else:
            mus = {
                label
                for label in solver.unsat_core()
                if isinstance(label, z3.BoolRef)
            }
            map.add(disjunction(*(negation(label) for label in mus)))
            yield mus
