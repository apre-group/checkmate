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
from constants import ANALYSIS_JSON_KEY, HONEST_HISTORY_JSON_KEY, PROPERTY_TO_JSON_KEY, SecurityProperty, \
    PROPERTY_TO_STR, GENERATED_PRECONDITIONS_JSON_KEY, JOINT_STRATEGIES_JSON_KEY, JOINT_STRATEGY_ORDERING_JSON_KEY, \
    JOINT_STRATEGY_STRATEGY_JSON_KEY
from utility import Utility, ZERO
from input import Tree, Leaf, Branch, Input


class StrategyChecker(metaclass=ABCMeta):
    """
    base class for checking strategies for security properties
    """
    to_check: Input
    _solver: z3.Solver

    def __init__(self,
                 checked_input: Input,
                 checked_honest_history: List[str],
                 strategy: Dict[str, str],
                 cases: List[Boolean],
                 generated_precondition_list: List[Boolean]) -> None:
        self.input = checked_input
        self.honest_history = checked_honest_history
        self.strategy = strategy
        self.cases = cases
        self.generated_preconditions = generated_precondition_list
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

    def _get_utilities(self, tree: Tree, players: Set[str], history: str, utilities: List[Utility]) -> List[Utility]:
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


class FeebleImmuneStrategyChecker(StrategyChecker):
    """checker for weak and weaker immunity"""

    @abstractmethod
    def _compare_utility(self, utility: Utility) -> z3.BoolRef:
        pass

    def utility_function(self, ut: Dict[str, Utility], players: Set[str]) -> List[Utility]:
        return [ut[p] for p in players]

    def _property_constraints(self) -> None:
        disjuncts = []

        for p in to_check.players:
            player_utilities = self._get_utilities(self.input.tree, {p}, '', [])
            disjuncts.extend([self._compare_utility(utility) for utility in player_utilities])

        self._solver.add(self.input.weak_immunity_constraints)
        self._solver.add(disjunction(*disjuncts))


class WeakImmunityStrategyChecker(FeebleImmuneStrategyChecker):
    """checker for weak immunity"""
    def _compare_utility(self, utility: Utility) -> z3.BoolRef:
        return utility < ZERO


class WeakerImmunityStrategyChecker(FeebleImmuneStrategyChecker):
    """checker for weaker immunity"""
    def _compare_utility(self, utility) -> z3.BoolRef:
        real_part = Utility.from_real(utility.real)
        return real_part < ZERO


class CollusionResilienceStrategyChecker(StrategyChecker):
    """checker for collusion resilience"""

    @staticmethod
    def strict_subgroups(group: Set) -> Iterator:
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
        disjuncts = False

        for player_subset in self.strict_subgroups(set(self.input.players)):
            sum_old_utility = sum(
                [self.input.tree.get_utility_of_terminal_history(self.honest_history)[pl] for pl in player_subset],
                start=ZERO)
            sum_new_utility = self._get_utilities(self.input.tree, set(self.input.players) - set(player_subset), '', [])

            for sum_utility in sum_new_utility:
                disjuncts = disjunction(sum_old_utility < sum_utility, disjuncts)

            self._solver.add(to_check.collusion_resilience_constraints)
            self._solver.add(disjuncts)


class PracticalityStrategyChecker(StrategyChecker):
    """checker for practicality"""

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
        disjuncts = []

        for subtree, history in self.walk_tree(self.input.tree, ''):
            if isinstance(subtree, Leaf):
                continue

            for player in self.input.players:
                old_utility = self.utility_of_strategy(subtree, history)[player]
                player_utilities = self._get_utilities(subtree, set(self.input.players) - {player}, history, [])
                disjuncts.extend([old_utility < utility for utility in player_utilities])

        self._solver.add(to_check.practicality_constraints)
        self._solver.add(disjunction(*disjuncts))


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
    to_check = Input(args.PATH)
    analysis_results = json.load(open(args.STRATEGIES))[ANALYSIS_JSON_KEY]
    logging.info(
        f"input OK, checking strategies..."
    )

    for analysis_result in analysis_results:
        honest_history = analysis_result[HONEST_HISTORY_JSON_KEY]

        for security_property in SecurityProperty:
            security_property_json = PROPERTY_TO_JSON_KEY[security_property]

            if security_property_json in analysis_result and \
                    analysis_result[security_property_json][JOINT_STRATEGIES_JSON_KEY]:
                logging.info(f"checking {PROPERTY_TO_STR[security_property]} of history {honest_history}")
                analysis_result_for_property = analysis_result[security_property_json]
                generated_preconditions = [to_check.load_constraint(c) for c in
                                           analysis_result_for_property[GENERATED_PRECONDITIONS_JSON_KEY]]

                for case_with_strategy in analysis_result_for_property[JOINT_STRATEGIES_JSON_KEY]:
                    ordering = case_with_strategy[JOINT_STRATEGY_ORDERING_JSON_KEY]

                    if ordering:
                        logging.info(f"- case {ordering}")

                    case_constraints = [to_check.load_constraint(c) for c in ordering]

                    joint_strategy = case_with_strategy[JOINT_STRATEGY_STRATEGY_JSON_KEY]
                    result = None

                    if security_property == SecurityProperty.WEAK_IMMUNITY:
                        result = WeakImmunityStrategyChecker(
                            to_check,
                            honest_history,
                            joint_strategy,
                            case_constraints,
                            generated_preconditions
                        ).check()

                    if security_property == SecurityProperty.WEAKER_IMMUNITY:
                        result = WeakerImmunityStrategyChecker(
                            to_check,
                            honest_history,
                            joint_strategy,
                            case_constraints,
                            generated_preconditions
                        ).check()

                    elif security_property == SecurityProperty.COLLUSION_RESILIENCE:
                        result = CollusionResilienceStrategyChecker(
                            to_check,
                            honest_history,
                            joint_strategy,
                            case_constraints,
                            generated_preconditions
                        ).check()

                    elif security_property == SecurityProperty.PRACTICALITY:
                        result = PracticalityStrategyChecker(
                            to_check,
                            honest_history,
                            joint_strategy,
                            case_constraints,
                            generated_preconditions
                        ).check()

                    if result is not None:
                        if result:
                            logging.info(f"--- strategy does satisfy {PROPERTY_TO_STR[security_property]}")
                        else:
                            logging.error(f"--- strategy does NOT satisfy {PROPERTY_TO_STR[security_property]}")
