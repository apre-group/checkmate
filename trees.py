# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
import itertools
import json

from typing import Any, Dict, Iterable, List, Union
import z3
from auxfunz3 import Boolean
from utility import Utility


class Tree(metaclass=ABCMeta):
    """base class for game trees"""

    @abstractmethod
    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        pass


class Leaf(Tree):
    """a leaf node"""
    utility: Dict[str, Utility]

    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        assert not history
        return self.utilities

    def __init__(self, utilities: Dict[str, Utility]):
        """initialise from a set of player utilities"""
        self.utilities = utilities

    def __repr__(self) -> str:
        return '\n'.join(
            f"{player}: {utility}"
            for player, utility in self.utilities.items()
        )


class Branch(Tree):
    """a non-leaf node with children"""
    player: str
    actions: Dict[str, Tree]

    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        assert len(history) > 0
        return self.actions[history[0]].get_utility_of_terminal_history(history[1:])

    def __init__(self, player: str, actions: Dict[str, Tree]):
        """initialise from a player (whose turn it is) and a set of actions"""
        self.player = player
        self.actions = actions

    def __repr__(self) -> str:
        # magic for pretty trees
        def pad(x: Iterable[str]) -> str:
            return '\n'.join(f"| {line}" for line in x)

        actions = '\n'.join(
            f"`>{action}\n{pad(repr(tree).splitlines())}"
            for action, tree in self.actions.items()
        )
        return f"{self.player}\n{actions}"


class Input:
    """an input problem"""
    players: List[str]
    actions: List[str]
    constants: Dict[str, Utility]
    initial_constraints: List[Boolean]
    weak_immunity_constraints: List[Boolean]
    weaker_immunity_constraints: List[Boolean]
    collusion_resilience_constraints: List[Boolean]
    practicality_constraints: List[Boolean]
    honest_histories: List[List[str]]
    tree: Tree

    def __init__(self, path: str):
        """try to load the file at `path`"""
        obj = json.load(open(path))
        self.players = obj['players']
        self.actions = obj['actions']
        # map from names to Utility, used for eval() later
        self.constants = {
            constant: Utility.from_name(constant, real)
            for constant, real in
            itertools.chain(
                ((constant, True) for constant in obj['constants']),
                ((constant, False) for constant in obj['infinitesimals'])
            )
        }
        self.initial_constraints = [
            self._load_constraint(constraint)
            for constraint in obj['initial_constraints']
        ]
        self.weak_immunity_constraints = [
            self._load_constraint(constraint)
            for constraint in obj['property_constraints']['weak_immunity']
        ]
        self.weaker_immunity_constraints = [
            self._load_constraint(constraint)
            for constraint in obj['property_constraints']['weaker_immunity']
        ]
        self.collusion_resilience_constraints = [
            self._load_constraint(constraint)
            for constraint in obj['property_constraints']['collusion_resilience']
        ]
        self.practicality_constraints = [
            self._load_constraint(constraint)
            for constraint in obj['property_constraints']['practicality']
        ]
        self.honest_histories = obj['honest_histories']
        self.tree = self._load_tree(obj['tree'])

    def __repr__(self) -> str:
        return (
            f"players: {self.players}\n"
            f"actions: {self.actions}\n"
            f"constants: {list(self.constants)}\n"
            f"initial constraints: {self.initial_constraints}\n"
            f"weak immunity constraints: {self.weak_immunity_constraints}\n"
            f"weaker immunity constraints: {self.weaker_immunity_constraints}\n"
            f"collusion resilience constraints: {self.collusion_resilience_constraints}\n"
            f"practicality constraints: {self.practicality_constraints}\n"
            f"honest histories: {self.honest_histories}\n"
            f"tree:\n{self.tree}"
        )

    def _load_utility(self, utility: Union[int, str]) -> Utility:
        """load a string expression or an integer into a Utility, via `eval()`"""
        if isinstance(utility, int):
            return Utility.from_real(utility)

        utility = eval(utility, {}, self.constants)
        # NB: "2 * 2" is a possibility
        if isinstance(utility, int):
            return Utility.from_real(utility)

        assert isinstance(utility, Utility)
        return utility

    def _load_constraint(self, source: str) -> Boolean:
        """load a string expression into a Boolean constraint, via `eval()`"""
        return eval(source, {'OR': z3.Or}, self.constants)

    def _load_tree(self, tree: Dict[str, Any]) -> Tree:
        """recursively load subtrees in the input"""
        if 'player' in tree:
            player = tree['player']
            children = {
                child['action']: self._load_tree(child['child'])
                for child in tree['children']
            }
            return Branch(player, children)
        else:
            utilities = {
                utility['player']: self._load_utility(utility['value'])
                for utility in tree['utility']
            }
            return Leaf(utilities)
