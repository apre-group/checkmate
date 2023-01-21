# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Optional, Union, Set, Generator
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


def eliminate_consequences(solver: z3.Solver, constraints: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    """compute a greedy consequence elimination of `constraints` wrt `solver`"""
    to_eliminate = set()
    for constr in constraints:
        to_check = constraints - to_eliminate - {constr} | {negation(constr)}
        if solver.check(*to_check) == z3.unsat:
            to_eliminate.add(constr)
    return constraints - to_eliminate


# following functions adapted from "Programming Z3"
def maximal_satisfying_subset(solver: z3.Solver,
                              start: Set[z3.BoolRef],
                              all_labels: Set[z3.BoolRef]) -> Set[z3.BoolRef]:
    """compute a maximal satisfying subset of `all_labels`, starting from `start` with respect to `solver`"""
    ps = all_labels - start
    mss = start
    backbones = set()

    while len(ps) > 0:
        p = ps.pop()
        if solver.check(*(mss | backbones | {p})) == z3.sat:
            model = solver.model()
            mss = mss | {p} | {
                q for q in ps
                if z3.is_true(model.eval(q))
            }
            ps = ps - mss
        else:
            backbones = backbones | {negation(p)}

    return mss


def minimal_unsat_cores(solver: z3.Solver, all_labels: Set[z3.BoolRef]) -> Generator[Set[z3.BoolRef], None, None]:
    """iteratively compute all minimal unsat cores in `all_labels` with respect to `solver`"""
    map_solver = z3.Solver()
    map_solver.set("unsat_core", True)
    map_solver.set("core.minimize", True)

    while map_solver.check() == z3.sat:
        model = map_solver.model()
        seed = {
            p for p in all_labels
            if not z3.is_false(model.eval(p))
        }
        if solver.check(*seed) == z3.sat:
            mss = maximal_satisfying_subset(solver, seed, all_labels)
            map_solver.add(disjunction(*(all_labels - mss)))
        else:
            mus = {
                label_expr
                for label_expr in solver.unsat_core()
                if isinstance(label_expr, z3.BoolRef)
            }
            map_solver.add(disjunction(*(negation(label_expr) for label_expr in mus)))
            yield mus
