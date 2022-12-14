# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Union
import z3
import operator
from auxfunz3 import Real, Boolean, LabelFn, negation, conjunction, disjunction, label


def flip(op: Callable[[Real, Real], Real]) -> Callable[[Real, Real], Real]:
    return lambda x, y: op(y, x)


def add(left: Real, right: Real) -> Real:
    """
    return left + right, except if either is 0
    """
    if type(left) == float and left == 0:
        return right
    elif type(right) == float and right == 0:
        return left
    else:
        return left + right


def sub(left: Real, right: Real) -> Real:
    """
    return left - right, except if either is 0
    """
    if type(left) == float and left == 0:
        return -right
    elif type(right) == float and right == 0:
        return left
    else:
        return left - right


def mul(left: Real, right: Real) -> Real:
    """
    return left * right, except if either is 1
    """
    if type(left) == float and left == 1:
        return right
    elif type(right) == float and right == 1:
        return left
    else:
        result = left * right
        # satisfy linter for some reason
        assert isinstance(result, float) or isinstance(result, z3.ArithRef)
        return result


class Utility:
    """
    a (real, infinitesimal) pair

    mostly just an adapter pattern for parsing via `eval()`
    and generating Z3 expressions by operator overloading
    """
    real: Real
    inf: Real

    def __init__(self, real: Real, inf: Real):
        """construct from real and infinitesimal parts"""
        self.real = real
        self.inf = inf

    @staticmethod
    def from_real(value: Real) -> Utility:
        """convert a numeric value into a real utility with zero infinitesimal"""
        return Utility(value, 0.0)

    @staticmethod
    def from_name(name: str, real: bool) -> Utility:
        """convert a string into a utility, either `real` or infinitesimal"""
        variable = z3.Real(name)
        return Utility(variable, 0.0) if real else Utility(0.0, variable)

    def __repr__(self) -> str:
        return f"<{self.real}, {self.inf}>"

    def __neg__(self) -> Utility:
        return Utility(-self.real, -self.inf)

    def __add__(self, other: Union[int, float, Utility]) -> Utility:
        return self._binary_expression(other, add)

    def __radd__(self, other: Union[int, float, Utility]) -> Utility:
        """useful when parsing e.g. 2 + p"""
        return self._binary_expression(other, flip(add))

    def __sub__(self, other: Union[int, float, Utility]) -> Utility:
        return self._binary_expression(other, sub)

    def __rsub__(self, other: Union[int, float, Utility]) -> Utility:
        """useful when parsing e.g. 2 - p"""
        return self._binary_expression(other, flip(sub))

    def __mul__(self, other: Union[int, float, Utility]) -> Utility:
        return self._binary_expression(other, mul)

    def __rmul__(self, other: Union[int, float, Utility]) -> Utility:
        """useful when parsing e.g. 2 * p"""
        return self._binary_expression(other, flip(mul))

    def __eq__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left == right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        if isinstance(other, int) or isinstance(other, float):
            other = Utility.from_real(other)

        return conjunction(
            label(self.real, other.real, operator.eq, label_fn, True),
            label(self.inf, other.inf, operator.eq, label_fn, False)
        )

    def __ne__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """`z3.Not(left == right)`"""
        return negation(self.__eq__(other, label_fn))

    def __gt__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left > right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        return self._binary_comparison(
            other, operator.gt, operator.gt, label_fn
        )

    def __ge__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left >= right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        return self._binary_comparison(
            other, operator.gt, operator.ge, label_fn
        )

    def __lt__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left < right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        return self._binary_comparison(
            other, operator.lt, operator.lt, label_fn
        )

    def __le__(
            self,
            other: Union[int, float, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left <= right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        return self._binary_comparison(
            other, operator.lt, operator.le, label_fn
        )

    def _binary_expression(
            self,
            other: Union[int, float, Utility],
            op: Callable[[Real, Real], Real]
    ) -> Utility:
        """generate a Z3 expression `left op right`"""
        if isinstance(other, int) or isinstance(other, float):
            other = Utility.from_real(other)

        return Utility(
            op(self.real, other.real),
            op(self.inf, other.inf)
        )

    def _binary_comparison(
            self,
            other: Union[int, float, Utility],
            real_op: Callable[[Real, Real], Boolean],
            inf_op: Callable[[Real, Real], Boolean],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left op right` using `real_op` and `inf_op` parts

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        if isinstance(other, int) or isinstance(other, float):
            other = Utility.from_real(other)

        return disjunction(
            label(self.real, other.real, real_op, label_fn, True),
            conjunction(
                label(self.real, other.real, operator.eq, label_fn, True),
                label(self.inf, other.inf, inf_op, label_fn, False)
            )
        )


ZERO = Utility.from_real(0.0)
"""the zero utility, <0.0, 0.0>"""
