from __future__ import annotations
import json
import sys
from typing import Dict, Tuple, Union
from enum import IntEnum

PLAYERS = ()
ACTIONS = ()
INFINITESIMALS = ()
CONSTANTS = ()
INITIAL_CONSTRAINTS = ()
WEAK_IMMUNITY_CONSTRAINTS = ()
COLLUSION_RESILIENCE_CONSTRAINTS = ()
PRACTICALITY_CONSTRAINTS = ()
HONEST_HISTORIES = ()
TREE = {}


class StringThing:
    def __init__(self, value: str):
        self.value = value

    def __repr__(self):
        return self.value

    def json(self):
        return self.value


class Action(StringThing):
    pass


class Player(StringThing):
    pass


class Constraint(StringThing):
    pass


class Precedence(IntEnum):
    ADDITION = 0,
    MULTIPLICATION = 1,
    LITERAL = 2


class Expr(StringThing):
    _precedence: Precedence

    def __init__(self, value: str, precedence: Precedence):
        super().__init__(value)
        self._precedence = precedence

    @staticmethod
    def precedence(expr: Union[Expr, float, int]) -> Precedence:
        if isinstance(expr, Expr):
            return expr._precedence
        else:
            return Precedence.LITERAL

    @staticmethod
    def parenthesise(expr: Union[Expr, float, int], precedence: Precedence) -> Union[Expr, float, int]:
        return expr if precedence <= Expr.precedence(expr) else Expr(f"({expr})", Precedence.LITERAL)

    @staticmethod
    def unary(expr: Union[Expr, float, int], precedence: Precedence, op: str) -> Expr:
        expr = Expr.parenthesise(expr, precedence)
        return Expr(f"{op}{expr}", precedence)

    @staticmethod
    def binary(left: Union[Expr, float, int], right: Union[Expr, float, int], precedence: Precedence, op: str) -> Expr:
        left = Expr.parenthesise(left, precedence)
        right = Expr.parenthesise(right, precedence)
        return Expr(f"{left} {op} {right}", precedence)

    def __add__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(self, other, Precedence.ADDITION, '+')

    def __radd__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(other, self, Precedence.ADDITION, '+')

    def __sub__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(self, other, Precedence.ADDITION, '-')

    def __rsub__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(other, self, Precedence.ADDITION, '-')

    def __mul__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(self, other, Precedence.MULTIPLICATION, '*')

    def __rmul__(self, other: Union[Expr, float, int]) -> Expr:
        return Expr.binary(other, self, Precedence.MULTIPLICATION, '*')

    def __neg__(self) -> Expr:
        return Expr.unary(self, Precedence.LITERAL, '-')

    def __ne__(self, other: Union[Expr, float, int]) -> Constraint:
        return Constraint(f"{self} != {other}")

    def __gt__(self, other: Union[Expr, float, int]) -> Constraint:
        return Constraint(f"{self} > {other}")

    def __ge__(self, other: Union[Expr, float, int]) -> Constraint:
        return Constraint(f"{self} >= {other}")


LExpr = Union[Expr, float, int]


class Tree:
    pass


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


def branch(player: Player, actions: Dict[Action, Tree]) -> Branch:
    return Branch(player, actions)


def players(*players: str) -> Tuple[Player, ...]:
    global PLAYERS
    PLAYERS = tuple(Player(player) for player in players)
    return PLAYERS


def actions(*actions: str) -> Tuple[Action, ...]:
    global ACTIONS
    ACTIONS = tuple(Action(action) for action in actions)
    return ACTIONS


def infinitesimals(*infs: str) -> Tuple[Expr, ...]:
    global INFINITESIMALS
    INFINITESIMALS = tuple(Expr(inf, Precedence.LITERAL) for inf in infs)
    return INFINITESIMALS


def constants(*constants: str) -> Tuple[Expr, ...]:
    global CONSTANTS
    CONSTANTS = tuple(Expr(constant, Precedence.LITERAL)
                      for constant in constants)
    return CONSTANTS


def initial_constraints(*constraints: Constraint):
    global INITIAL_CONSTRAINTS
    INITIAL_CONSTRAINTS = constraints


def weak_immunity_constraints(*constraints: Constraint):
    global WEAK_IMMUNITY_CONSTRAINTS
    WEAK_IMMUNITY_CONSTRAINTS = constraints


def collusion_resilience_constraints(*constraints: Constraint):
    global COLLUSION_RESILIENCE_CONSTRAINTS
    COLLUSION_RESILIENCE_CONSTRAINTS = constraints


def practicality_constraints(*constraints: Constraint):
    global PRACTICALITY_CONSTRAINTS
    PRACTICALITY_CONSTRAINTS = constraints


def honest_histories(*histories: Tuple[Action, ...]):
    global HONEST_HISTORIES
    HONEST_HISTORIES = histories


def tree(tree: Tree):
    global TREE
    TREE = tree


def finish():
    json.dump({
        'players': PLAYERS,
        'actions': ACTIONS,
        'infinitesimals': INFINITESIMALS,
        'constants': CONSTANTS,
        'initial_constraints': INITIAL_CONSTRAINTS,
        'property_constraints': {
            'weak_immunity': WEAK_IMMUNITY_CONSTRAINTS,
            'collusion_resilience': COLLUSION_RESILIENCE_CONSTRAINTS,
            'practicality': PRACTICALITY_CONSTRAINTS
        },
        'honest_histories': HONEST_HISTORIES,
        'tree': TREE
    }, default=lambda x: x.json(), fp=sys.stdout, indent=2)
