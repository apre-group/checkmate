# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Union
import z3

Real = Union[float, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]


def not_(to_negate: Boolean) -> z3.BoolRef:
    """negate a Z3 expression while satisfying the type checker"""
    negated = z3.Not(to_negate)
    assert isinstance(negated, z3.BoolRef)
    return negated


def or_(*disjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 disjunction while satisfying the type checker"""
    result = z3.Or(disjuncts)
    assert isinstance(result, z3.BoolRef)
    return result


def and_(*conjuncts: Boolean) -> z3.BoolRef:
    """build a Z3 conjunction while satisfying the type checker"""
    result = z3.And(conjuncts)
    assert isinstance(result, z3.BoolRef)
    return result


def imp(left: Boolean, right: Boolean) -> z3.BoolRef:
    """build a Z3 implication while satisfying the type checker"""
    return z3.Implies(left, right)
