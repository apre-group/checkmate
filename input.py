# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
import itertools
import json

from typing import Any, Dict, Iterable, List, Union, Tuple
import z3
from auxfunz3 import Boolean
from constants import CONSTRAINT_FUNS
from utility import Utility


class Tree(metaclass=ABCMeta):
    """base class for game trees"""

    @abstractmethod
    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        pass


class Leaf(Tree):
    """a leaf node"""
    utility: Dict[str, Utility]
    condition: Boolean

    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        assert not history
        return self.utilities

    def __init__(self, condition: Boolean, utilities: Dict[str, Utility]):
        """initialise from a set of player utilities"""
        self.utilities = utilities
        self.condition = condition

    def __repr__(self) -> str:
        return '\n'.join(
            f"{player}: {utility}"
            for player, utility in self.utilities.items()
        )


class Branch(Tree):
    """a non-leaf node with children"""
    player: str
    condition: Boolean
    actions: Dict[str, Tree]

    def get_player(self) -> str:
        return self.player

    def get_utility_of_terminal_history(self, history: List[str]) -> Dict[str, Utility]:
        assert len(history) > 0
        return self.actions[history[0]].get_utility_of_terminal_history(history[1:])

    def __init__(self, player: str, condition: Boolean, actions: Dict[str, Tree]):
        """initialise from a player (whose turn it is) and a set of actions"""
        self.player = player
        self.condition = condition
        self.actions = actions

    def __repr__(self) -> str:
        # magic for pretty trees
        def pad(x: Iterable[str]) -> str:
            return '\n'.join(f"| {line}" for line in x)

        actions = '\n'.join(
            f"`>{action}, if {tree.condition}\n{pad(repr(tree).splitlines())}"
            for action, tree in self.actions.items()
        )
        return f"{self.player}\n{actions}"


class HistoryTree:
    """class for history trees"""

    def __init__(self, action_name: str, condition: z3.BoolRef, children: List[HistoryTree]):
        self.action = action_name
        self.condition = condition
        self.children = children

    def __repr__(self) -> str:
        # magic for pretty trees
        def pad(x: Iterable[str]) -> str:
            return '\n'.join(f"| {line}" for line in x)

        offspring = '\n'.join(
            f"`>{pad(repr(tree).splitlines())}"
            for tree in self.children
        )
        return f"{self.action} if {self.condition}\n{offspring}"

    def json(self):
        return self.__repr__()


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
    honest_histories: List[HistoryTree]
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
            self.load_constraint(constraint)
            for constraint in obj['initial_constraints']
        ]
        self.weak_immunity_constraints = [
            self.load_constraint(constraint)
            for constraint in obj['property_constraints']['weak_immunity']
        ]
        self.weaker_immunity_constraints = [
            self.load_constraint(constraint)
            for constraint in obj['property_constraints']['weaker_immunity']
        ]
        self.collusion_resilience_constraints = [
            self.load_constraint(constraint)
            for constraint in obj['property_constraints']['collusion_resilience']
        ]
        self.practicality_constraints = [
            self.load_constraint(constraint)
            for constraint in obj['property_constraints']['practicality']
        ]
        self.tree = self._load_tree(obj['tree'])
        self.honest_histories = [self._load_history_tree(t, self.tree) for t in obj['honest_histories']]


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

    def load_constraint(self, source: str) -> Boolean:
        """load a string expression into a Boolean constraint, via `eval()`"""
        return eval(source, CONSTRAINT_FUNS, self.constants)

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

    def _load_tree(self, tree: Dict[str, Any]) -> Tree:
        """recursively load subtrees in the input"""
        if 'player' in tree:
            player = tree['player']
            try:
                condition = self.load_constraint(tree['condition'])
            except KeyError:
                condition = True
            children = {
                child['action']: self._load_tree(child['child'])
                for child in tree['children']
            }
            return Branch(player, condition, children)
        else:
            try:
                condition = self.load_constraint(tree['condition'])
            except KeyError:
                condition = True
            utilities = {
                utility['player']: self._load_utility(utility['value'])
                for utility in tree['utility']
            }
            return Leaf(condition, utilities)

    def _load_history_tree(self, hist_tree: Dict[str, Any], tree: Tree) -> HistoryTree:
        """recursively load history subtrees in the input"""
        if hist_tree['action'] == '':
            condition = True
        else:
            condition = tree.condition
        children = [self._load_history_tree(child, tree.actions[child['action']]) for child in hist_tree["children"]]
        return HistoryTree(hist_tree["action"], condition, children)

    def get_tree(self) -> Tree:
        return self.tree

    def get_players_in_hist(self, Tree, history: List(str)) -> List(str):
        """get the players along the provided history"""
        if len(history) == 0:
            return []
        else:
            assert type(Tree) == Branch
            player_list = [Tree.get_player()]
            player_list.extend(self.get_players_in_hist(Tree.actions[history[0]],history[1:]))
            return player_list

    def get_player_at_hist(self, tree, history: List[str]) -> str:
        """get the player at the node of the history"""
        if len(history) == 0:
            assert isinstance(tree, Branch)
            return tree.get_player()
        else:
            return self.get_player_at_hist(tree.actions[history[0]], history[1:])

    def get_subtree_at_hist(self, tree: Tree, history: List[str]) -> Tree:
        if len(history) == 0:
            return tree
        else:
            assert isinstance(tree, Branch)
            return self.get_subtree_at_hist(tree.actions[history[0]], history[1:])
