# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from typing import Callable, Union
import z3
import operator
from auxfunz3 import Real, Boolean, not_, and_, or_


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

    def __add__(self, other: Union[float, Utility]) -> Utility:
        if not isinstance(other, Utility):
            return Utility(self.real + other, self.inf)

        return Utility(
            self.real + other.real,
            self.inf + other.inf
        )

    def __radd__(self, other: float) -> Utility:
        """useful when parsing e.g. 2 + p"""
        return Utility(other + self.real, self.inf)

    def __sub__(self, other: Union[float, Utility]) -> Utility:
        if not isinstance(other, Utility):
            return Utility(self.real - other, self.inf)

        return Utility(
            self.real - other.real,
            self.inf - other.inf
        )

    def __rsub__(self, other: float) -> Utility:
        """useful when parsing e.g. 2 - p"""
        return Utility(other - self.real, -self.inf)

    def __mul__(self, other: float) -> Utility:
        assert not isinstance(other, Utility)
        return Utility(
            other * self.real,
            other * self.inf
        )

    def __rmul__(self, other: float) -> Utility:
        """useful when parsing e.g. 2 * p"""
        return Utility(other * self.real, other * self.inf)

    def __eq__(self, other: Union[float, Utility]) -> z3.BoolRef:
        """generate a Z3 constraint `left == right`"""
        if not isinstance(other, Utility):
            other = Utility.from_real(other)

        return and_(
            self.real == other.real,
            self.inf == other.inf
        )

    def __ne__(self, other: Union[float, Utility]) -> z3.BoolRef:
        return not_(self == other)

    def __gt__(self, other: Union[float, Utility]) -> z3.BoolRef:
        """generate a Z3 constraint `left > right`"""
        return self._binary_comparison(other, operator.gt, operator.gt)

    def __ge__(self, other: Union[float, Utility]) -> z3.BoolRef:
        """generate a Z3 constraint `left >= right`"""
        return self._binary_comparison(other, operator.gt, operator.ge)

    def __lt__(self, other: Union[float, Utility]) -> z3.BoolRef:
        """generate a Z3 constraint `left < right`"""
        return self._binary_comparison(other, operator.lt, operator.lt)

    def __le__(self, other: Union[float, Utility]) -> z3.BoolRef:
        """generate a Z3 constraint `left <= right`"""
        return self._binary_comparison(other, operator.lt, operator.le)

    def _binary_expression(self, other: Union[float, Utility], op: Callable[[Real, Real], Real]) -> Utility:
        """generate a Z3 expression `left op right`"""
        if not isinstance(other, Utility):
            other = Utility.from_real(other)

        return Utility(
            op(self.real, other.real),
            op(self.inf, other.inf)
        )

    def _binary_comparison(
        self,
        other: Union[float, Utility],
        real_op: Callable[[Real, Real], Boolean],
        inf_op: Callable[[Real, Real], Boolean]
    ) -> z3.BoolRef:
        """generate a Z3 constraint `left op right` using `real_op` and `inf_op` parts"""
        if not isinstance(other, Utility):
            other = Utility.from_real(other)

        return or_(
            real_op(self.real, other.real),
            and_(
                self.real == other.real,
                inf_op(self.inf, other.inf)
            )
        )


ZERO = Utility.from_real(0.0)
"""the zero utility, <0.0, 0.0>"""
