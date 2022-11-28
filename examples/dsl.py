from __future__ import annotations
import json
from typing import Dict, Union, List
from enum import IntEnum


class StringThing:
    value: str

    def __init__(self, value: str):
        self.value = value

    def __repr__(self):
        return self.value

    def __str__(self):
        return self.value

    def json(self):
        return repr(self)


class Action(StringThing):
    pass


class Player(StringThing):
    pass


class Precedence(IntEnum):
    ADDITION = 0,
    SUBTRACTION = 1,
    MULTIPLICATION = 2,
    HIGHEST = 3


class Expr:
    precedence: Precedence

    def __init__(self, precedence: Precedence):
        self.precedence = precedence

    def __add__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(self, other, '+')

    def __radd__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(other, self, '+')

    def __sub__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(self, other, '-')

    def __rsub__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(other, self, '-')

    def __mul__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(self, other, '*')

    def __rmul__(self, other: Union[Expr, float, int]) -> Expr:
        return binary_expr(other, self, '*')

    def __neg__(self) -> Expr:
        return negate_expr(self)

    def __ne__(self, other: Union[Expr, float, int]) -> Constraint:
        return DisequationConstraint('!=', self, other)

    def __gt__(self, other: Union[Expr, float, int]) -> Constraint:
        return DisequationConstraint('>', self, other)

    def __ge__(self, other: Union[Expr, float, int]) -> Constraint:
        return DisequationConstraint('>=', self, other)

    def json(self):
        return repr(self)


LExpr = Union[Expr, float, int]


def precedence_of(expr: LExpr) -> Precedence:
    return expr.precedence if isinstance(expr, Expr) else Precedence.HIGHEST


class NameExpr(Expr):
    name: str

    def __init__(self, name: str):
        super().__init__(Precedence.HIGHEST)
        self.name = name

    def __repr__(self):
        return self.name


class ParenExpr(Expr):
    expr: LExpr

    def __init__(self, expr: LExpr):
        super().__init__(Precedence.HIGHEST)
        self.expr = expr

    def __repr__(self):
        return f"({self.expr})"


def parenthesise_expr(expr: LExpr, precedence: Precedence) -> Union[Expr, float, int]:
    return expr if precedence <= precedence_of(expr) else ParenExpr(expr)


class NegateExpr(Expr):
    expr: LExpr

    def __init__(self, expr: LExpr):
        super().__init__(Precedence.HIGHEST)
        self.expr = expr

    def __repr__(self):
        return f"-{self.expr}"


def negate_expr(expr: LExpr) -> Expr:
    expr = parenthesise_expr(expr, Precedence.HIGHEST)
    return NegateExpr(expr)


BINARY_OP_PRECEDENCES = {
    '+': (Precedence.ADDITION, Precedence.ADDITION, Precedence.ADDITION),
    '-': (Precedence.ADDITION, Precedence.SUBTRACTION, Precedence.ADDITION),
    '*': (Precedence.MULTIPLICATION, Precedence.MULTIPLICATION, Precedence.MULTIPLICATION)
}


class BinaryExpr(Expr):
    op: str
    left: LExpr
    right: LExpr

    def __init__(self, op: str, precedence: Precedence, left: LExpr, right: LExpr):
        super().__init__(precedence)
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return f"{self.left} {self.op} {self.right}"


def binary_expr(left: LExpr, right: LExpr, op: str) -> Expr:
    lprec, rprec, precedence = BINARY_OP_PRECEDENCES[op]
    left = parenthesise_expr(left, lprec)
    right = parenthesise_expr(right, rprec)
    return BinaryExpr(op, precedence, left, right)


class Tree:
    def graphviz(self):
        raise NotImplementedError()


class Leaf(Tree):
    def __init__(self, utilities: Dict[Player, LExpr]):
        self.utilities = utilities

    def json(self):
        return {
            'utility': [
                {'player': player, 'value': utility}
                for player, utility in self.utilities.items()
            ]
        }

    def graphviz(self):
        print(f'\tn{id(self)} [label="*"];')
        for player, utility in self.utilities.items():
            print(f'\tn{id(self)}_{player} [label="{utility}"];')
            print(f'\tn{id(self)} -> n{id(self)}_{player} [label="{player}"];')


def leaf(utilities: Dict[Player, LExpr]) -> Leaf:
    return Leaf(utilities)


class Branch(Tree):
    def __init__(self, player: Player, actions: Dict[Action, Tree]):
        self.player = player
        self.actions = actions

    def json(self):
        return {
            'player': self.player,
            'children': [
                {'action': action, 'child': child}
                for action, child in self.actions.items()
            ]
        }

    def graphviz(self):
        print(f'\tn{id(self)} [label="{self.player}"];')
        for (action, child) in self.actions.items():
            child.graphviz()
            print(f'\tn{id(self)} -> n{id(child)} [label="{action}"];')


def branch(player: Player, actions: Dict[Action, Tree]) -> Branch:
    return Branch(player, actions)


def players(*players: str) -> List[Player]:
    return [Player(player) for player in players]


def actions(*actions: str) -> List[Action]:
    return [Action(action) for action in actions]


def infinitesimals(*infs: str) -> List[Expr]:
    return [NameExpr(inf) for inf in infs]


def constants(*constants: str) -> List[Expr]:
    return [NameExpr(constant) for constant in constants]


class Constraint:
    def json(self):
        return repr(self)


class DisequationConstraint(Constraint):
    op: str
    left: LExpr
    right: LExpr

    def __init__(self, op: str, left: LExpr, right: LExpr):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return f"{self.left} {self.op} {self.right}"


def finish(
    players: List[Player],
    actions: List[Action],
    infinitesimals: List[Expr],
    constants: List[Expr],
    initial_constraints: List[Constraint],
    weak_immunity_constraints: List[Constraint],
    collusion_resilience_constraints: List[Constraint],
    practicality_constraints: List[Constraint],
    honest_histories: List[List[Action]],
    tree: Tree,
):
    import sys
    mode = sys.argv[1] if len(sys.argv) >= 2 else ''
    if mode == 'graphviz':
        print("digraph tree {")
        tree.graphviz()
        print("}")
    else:
        json.dump({
            'players': players,
            'actions': actions,
            'infinitesimals': infinitesimals,
            'constants': constants,
            'initial_constraints': initial_constraints,
            'property_constraints': {
                'weak_immunity': weak_immunity_constraints,
                'collusion_resilience': collusion_resilience_constraints,
                'practicality': practicality_constraints
            },
            'honest_histories': honest_histories,
            'tree': tree
        }, default=lambda x: x.json(), fp=sys.stdout, indent=2)

    sys.exit(0)
