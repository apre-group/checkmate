from __future__ import annotations
import json
import sys
from typing import Dict, Tuple, Union

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


class Expr(StringThing):
    def __add__(self, other: Union[Expr, float]) -> Expr:
        return Expr(f"{self} + {other}")

    def __sub__(self, other: Union[Expr, float]) -> Expr:
        return Expr(f"{self} - {other}")

    def __neg__(self) -> Expr:
        return Expr(f"-{self}")

    def __ne__(self, other: Union[Expr, float]) -> Constraint:
        return Constraint(f"{self} != {other}")

    def __gt__(self, other: Union[Expr, float]) -> Constraint:
        return Constraint(f"{self} > {other}")

    def __ge__(self, other: Union[Expr, float]) -> Constraint:
        return Constraint(f"{self} >= {other}")


class Tree:
    pass


class Leaf(Tree):
    def __init__(self, utilities: Dict[Player, Union[Expr, float]]):
        self.utilities = utilities

    def json(self):
        return {
            'utility': [
                {'player': player, 'value': utility}
                for player, utility in self.utilities.items()
            ]
        }


def leaf(utilities: Dict[Player, Union[Expr, float]]) -> Leaf:
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
    INFINITESIMALS = tuple(Expr(inf) for inf in infs)
    return INFINITESIMALS


def constants(*constants: str) -> Tuple[Expr, ...]:
    global CONSTANTS
    CONSTANTS = tuple(Expr(constant) for constant in constants)
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