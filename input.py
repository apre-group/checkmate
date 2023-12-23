# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

import itertools
import json
import logging
from typing import Any, Optional, Union
import z3

from auxfunz3 import Boolean
from trees import Tree, Leaf, Branch
from utility import Utility

class Input:
    """an input problem"""
    players: list[str]
    """the players in the game"""
    constants: dict[str, Utility]
    """the real-valued constants"""
    initial_constraints: list[Boolean]
    """initial constraints from the problem"""
    weak_immunity_constraints: list[Boolean]
    """weak immunity initial constraints from the problem"""
    weaker_immunity_constraints: list[Boolean]
    """weaker immunity initial constraints from the problem"""
    collusion_resilience_constraints: list[Boolean]
    """collusion resilience initial constraints from the problem"""
    practicality_constraints: list[Boolean]
    """practicality initial constraints from the problem"""
    honest_histories: list[list[str]]
    """possible honest histories"""
    tree: Tree
    """the game tree"""
    honest_utilities: Optional[dict[str, Utility]]
    """the current utilities on the honest path"""

    def __init__(self, path: str):
        """try to load the file at `path`"""
        obj = json.load(open(path))
        self.players = obj['players']
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
        self.honest_utilities = None

    def __repr__(self) -> str:
        return (
            f"players: {self.players}\n"
            f"constants: {list(self.constants)}\n"
            f"initial constraints: {self.initial_constraints}\n"
            f"weak immunity constraints: {self.weak_immunity_constraints}\n"
            f"weaker immunity constraints: {self.weaker_immunity_constraints}\n"
            f"collusion resilience constraints: {self.collusion_resilience_constraints}\n"
            f"practicality constraints: {self.practicality_constraints}\n"
            f"honest histories: {self.honest_histories}\n"
            f"tree:\n{self.tree}"
        )

    def _load_constraint(self, source: str) -> Boolean:
        """load a string expression into a Boolean constraint, via `eval()`"""
        return eval(source, {'Or': z3.Or, 'And': z3.And}, self.constants)

    def _load_utility(self, utility: Union[int, float, str]) -> Utility:
        """load a string expression or a number into a Utility, via `eval()`"""
        if not isinstance(utility, str):
            return Utility.from_real(utility)

        utility = eval(utility, {}, self.constants)
        # NB: "2 * 2" is a possible string
        if not isinstance(utility, Utility):
            return Utility.from_real(float(utility))

        assert isinstance(utility, Utility)
        return utility

    def _load_tree(self, tree: dict[str, Any]) -> Tree:
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

    def start_honest_history(self, honest_history: list[str]):
        """start work on a new honest history"""
        self.tree.reset_honest()
        self.honest_utilities = self.tree.mark_honest(honest_history)

    def property(self, property: str):
        """determine if the input has some property for the current honest history"""

        assert self.honest_utilities is not None
        logging.info(property)
        solver = z3.Solver()
        solver.add(*self.initial_constraints)
        assert solver.check() == z3.sat

        if property == 'weak_immunity' or property == 'weaker_immunity':
            weaker = property == 'weaker_immunity'
            if weaker:
                solver.add(*self.weaker_immunity_constraints)
            else:
                solver.add(*self.weak_immunity_constraints)
            for player in self.players:
                logging.info(f"player {player}")
                if not self.tree.weak_immune(solver, player, weaker):
                    print("failed, split:", self.tree.reason)
        elif property == 'collusion_resilience':
            solver.add(*self.collusion_resilience_constraints)
            for group_size in range(1, len(self.players)):
                for group in itertools.combinations(self.players, group_size):
                    logging.info(f"group {group}")
                    honest = sum(self.honest_utilities[player] for player in group)
                    if not self.tree.collusion_resilient(solver, group, honest):
                        print("failed, split:", self.tree.reason)
        elif property == 'practicality':
            solver.add(*self.collusion_resilience_constraints)
            if not self.tree.practical(solver):
                print("failed, split:", self.tree.reason)

        self.tree.reset_strategy()
