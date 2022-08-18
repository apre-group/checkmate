# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Optional, Union
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