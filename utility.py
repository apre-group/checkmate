# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Union
import z3
import operator
from auxfunz3 import Real, Boolean, LabelFn, negation, conjunction, disjunction, label


def binary_op_with_id(
        left: Real,
        right: Real,
        op: Callable[[Real, Real], Real],
        id: float
) -> Real:
    """
    build the expression `op(left, right)`

    optimisation: if either side is `id`, this returns the other side
    """
    if type(left) == float and left == id:
        return right
    elif type(right) == float and right == id:
        return left
    else:
        return op(left, right)


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
    def from_int(value: int) -> Utility:
        """convert an integer into a real utility with zero infinitesimal"""
        return Utility(float(value), 0.0)

    @staticmethod
    def from_name(name: str, real: bool) -> Utility:
        """convert a string into a utility, either `real` or infinitesimal"""
        variable = z3.Real(name)
        return Utility(variable, 0.0) if real else Utility(0.0, variable)

    def __repr__(self) -> str:
        return f"<{self.real}, {self.inf}>"

    def __neg__(self) -> Utility:
        return Utility(-self.real, -self.inf)

    # TODO __radd__, __rsub__?
    def __add__(self, other: Union[int, Utility]) -> Utility:
        return self._binary_expression(other, operator.add, 0.0)

    def __sub__(self, other: Union[int, Utility]) -> Utility:
        return self._binary_expression(-other, operator.add, 0.0)

    def __mul__(self, other: Union[int, Utility]) -> Utility:
        return self._binary_expression(other, operator.mul, 1.0)

    def __rmul__(self, other: Union[int, Utility]) -> Utility:
        """useful when parsing e.g. 2 * p"""
        return self.__mul__(other)

    def __eq__(
            self,
            other: Union[int, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left == right`

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        if isinstance(other, int):
            other = Utility.from_int(other)

        return conjunction(
            label(self.real, other.real, operator.eq, label_fn, True),
            label(self.inf, other.inf, operator.eq, label_fn, False)
        )

    def __ne__(
            self,
            other: Union[int, Utility],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """`z3.Not(left == right)`"""
        return negation(self.__eq__(other, label_fn))

    def __gt__(
            self,
            other: Union[int, Utility],
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
            other: Union[int, Utility],
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
            other: Union[int, Utility],
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
            other: Union[int, Utility],
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
            other: Union[int, Utility],
            op: Callable[[Real, Real], Real],
            id: float
    ) -> Utility:
        """generate a Z3 expression `left op right` via `binary_op_with_id`"""
        if isinstance(other, int):
            other = Utility.from_int(other)

        return Utility(
            binary_op_with_id(self.real, other.real, op, id),
            binary_op_with_id(self.inf, other.inf, op, id)
        )

    def _binary_comparison(
            self,
            other: Union[int, Utility],
            real_op: Callable[[Real, Real], Boolean],
            inf_op: Callable[[Real, Real], Boolean],
            label_fn: LabelFn = None
    ) -> z3.BoolRef:
        """
        generate a Z3 constraint `left op right` using `real_op` and `inf_op` parts

        when `label_fn` is supplied, label generated comparisons for unsat cores
        """
        if isinstance(other, int):
            other = Utility.from_int(other)

        return disjunction(
            label(self.real, other.real, real_op, label_fn, True),
            conjunction(
                label(self.real, other.real, operator.eq, label_fn, True),
                label(self.inf, other.inf, inf_op, label_fn, False)
            )
        )


ZERO = Utility.from_int(0)
"""the zero utility, <0.0, 0.0>"""