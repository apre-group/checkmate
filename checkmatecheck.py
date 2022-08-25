#!/usr/bin/env python3

# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from argparse import ArgumentParser
import itertools
import json
import logging
from typing import Dict, List, Set, Tuple, Iterator
import z3

from auxfunz3 import Boolean, disjunction
from utility import Utility, ZERO
from trees import Tree, Leaf, Branch, Input


class StrategyChecker(metaclass=ABCMeta):
    """
    base class for checking strategies for security properties
    """
    input: Input
    _solver: z3.Solver

    def __init__(self, input: Input, honest_history: List[str], strategy: Dict[str, str], cases: List[Boolean], generated_preconditions: List[Boolean]) -> None:
        self.input = input
        self.honest_history = honest_history
        self.strategy = strategy
        self.cases = cases
        self.generated_preconditions = generated_preconditions
        self._solver = z3.Solver()

        self._solver.add(self.input.initial_constraints)
        self._solver.add(self.cases)
        self._solver.add(self.generated_preconditions)

    @abstractmethod
    def utility_function(self, ut: Dict[str, Utility], players: Set[str]) -> List[Utility]:
        pass

    @abstractmethod
    def _property_constraints(self) -> None:
        pass

    def _get_utilities(self, tree: Tree, players: Set[str], history: str, utilities: List[Utility])-> List[Utility]:
        if isinstance(tree, Branch):
            if tree.player in players:
                # it's one of the fixed players' turn
                action = self.strategy[history]
                child = tree.actions[action]
                history = history + ";" + action if history else action
                return self._get_utilities(child, players, history, utilities)

            else:
                # it's another player's turn
                for action, child in tree.actions.items():
                    history1 = history + ";" + action if history else action
                    utilities.extend(
                       self._get_utilities(child, players, history1, utilities))

        elif isinstance(tree, Leaf):
            # leaf node -> apply function to node
            return self.utility_function(tree.utilities, players)

        else:
            raise Exception('Encountered unknown type of node!')

        return utilities

    def check(self) -> bool:
        self._property_constraints()
        if self._solver.check() == z3.unsat:
            return True
        else:
            return False


class WeakImuneStrategyChecker(StrategyChecker):
    """checker for weak immunity"""

    def utility_function(self, ut: Dict[str, Utility], players: Set[str]) -> List[Utility]:
        return [ut[p] for p in players]

    def _property_constraints(self) -> None:
        disj = []

        for p in input.players:
            player_utilities = self._get_utilities(self.input.tree, {p}, '', [])
            disj.extend([ZERO > utility for utility in player_utilities])

        self._solver.add(self.input.weak_immunity_constraints)
        self._solver.add(disjunction(*disj))


class CollusionResilienceStrategyChecker(StrategyChecker):

    def strict_subgroups(self, group: Set) -> Iterator:
        """
        Generator for all non-empty subgroups of a set of players.
        """
        return (
            subset
            for length in range(1, len(group))
            for subset in itertools.combinations(group, length)
        )

    def utility_function(self, ut: Dict[str, Utility], players: Set[str]) -> List[Utility]:
        return [sum([ut[player] for player in set(self.input.players) - players], start=ZERO)]

    def _property_constraints(self) -> None:
        disj = False

        for player_subset in self.strict_subgroups(set(self.input.players)):
            sum_old_utility = sum([self.input.tree.get_utility_of_terminal_history(self.honest_history)[pl] for pl in player_subset], start=ZERO)
            sum_new_utility = self._get_utilities(self.input.tree, set(self.input.players) - set(player_subset), '', [])

            for sum_utility in sum_new_utility:
                disj = disjunction(sum_old_utility < sum_utility, disj)

            self._solver.add(input.collusion_resilience_constraints)
            self._solver.add(disj)


class PracticalityStrategyChecker(StrategyChecker):

    def utility_function(self, ut: Dict[str, Utility], players: Set[str]) -> List[Utility]:
        return [ut[p] for p in set(self.input.players) - players]

    def utility_of_strategy(self, tree: Tree, history: str) -> Dict[str, Utility]:
        if isinstance(tree, Leaf):
            return tree.utilities
        elif isinstance(tree, Branch):
            action = self.strategy[history]
            new_history = history + ";" + action if history else action
            return self.utility_of_strategy(tree.actions[action], new_history)
        else:
            raise Exception(f"{tree} is not a valid tree")

    def walk_tree(self, tree: Tree, history: str) -> Iterator[Tuple[Tree, str]]:
        yield tree, history

        if isinstance(tree, Branch):
            for action, child in tree.actions.items():
                new_history = history + ";" + action if history else action
                yield from self.walk_tree(child, new_history)

    def _property_constraints(self) -> None:

        disj = []
        for subtree, history in self.walk_tree(self.input.tree, ''):
            if isinstance(subtree, Leaf):
                continue

            for player in self.input.players:
                old_utility = self.utility_of_strategy(subtree, history)[player]
                player_utilities = self._get_utilities(subtree, set(self.input.players) - {player}, history, [])
                disj.extend([old_utility < utility for utility in player_utilities])

        self._solver.add(input.practicality_constraints)
        self._solver.add(disjunction(*disj))


if __name__ == '__main__':
    logging.basicConfig(
        level=logging.INFO,
        format='[%(levelname)s] %(message)s'
    )
    parser = ArgumentParser(
        description="check strategies of off-chain protocols"
    )
    parser.add_argument(
        'PATH',
        type=str,
        help="path to input file"
    )
    parser.add_argument(
        'STRATEGIES',
        type=str,
        help="path to file with strategies"
    )
    args = parser.parse_args()
    input = Input(args.PATH)
    strategies = json.load(open(args.STRATEGIES))['strategies']
    logging.info(
        f"input OK, checking strategies..."
    )

    for honest_history in strategies:
        for pr in ["weak_immunity", "collusion_resilience", "practicality"]:
            logging.info(f"checking {pr.replace('_', ' ')} of history {honest_history['history']}")
            gen_prec_str = honest_history[pr]["generated_preconditions"]
            generated_preconditions = [input._load_constraint(c) for c in gen_prec_str]
            for case in honest_history[pr]["cases"]:
                logging.info(f"case {case['case']}")
                case_constraints = [input._load_constraint(c) for c in case['case']]
                if pr == "weak_immunity":
                    result = WeakImuneStrategyChecker(
                        input,
                        honest_history['history'],
                        case['strategy'],
                        case_constraints,
                        generated_preconditions
                    ).check()
                    print(result)
                elif pr == "collusion_resilience":
                    result = CollusionResilienceStrategyChecker(
                        input,
                        honest_history['history'],
                        case['strategy'],
                        case_constraints,
                        generated_preconditions
                    ).check()
                    print(result)
                elif pr == "practicality":
                    result = PracticalityStrategyChecker(
                        input,
                        honest_history['history'],
                        case['strategy'],
                        case_constraints,
                        generated_preconditions
                    ).check()
                    print(result)
