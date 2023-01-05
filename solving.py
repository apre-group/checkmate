# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from typing import Any, Dict, List, Tuple
import itertools
import logging

from auxfunz3 import *
from utility import Utility, ZERO
from trees import Tree, Leaf, Branch, Input


class StrategySolver(metaclass=ABCMeta):
    """
    base class for generating strategies from constraints

    subclasses override a few functions and use provided methods
    to implement e.g. weak immunity
    """
    input: Input
    checked_history: List[str]
    generate_preconditions: bool
    generate_counterexamples: bool
    _solver: z3.Solver

    # maintain a bijection from (left, right) expression pairs and Z3 labels
    _pair2label: Dict[Tuple[Real, Real], z3.BoolRef]
    # note extra boolean to partition comparisons into real/infinitesimal
    _label2pair: Dict[z3.BoolRef, Tuple[Real, Real, bool]]

    # maintain a bijection from (player, history) pairs and Z3 labels
    _subtree2label: Dict[Tuple[Tuple[str], Tuple[str]], z3.BoolRef]
    _label2subtree: Dict[z3.BoolRef, Tuple[Tuple[str], Tuple[str]]]

    # mapping from action variables to (history, action) pairs
    _action_variables: Dict[z3.BoolRef, Tuple[List[str], str]]

    # set of variables to exclude from case splits: useful for e.g. utility variables
    _exclude_variables: Set[Real]

    # the set of generated preconditions in case the game is not secure per se
    # TODO does this need to be a member?
    _generated_preconditions: Set[z3.BoolRef]

    @abstractmethod
    def _property_initial_constraints(self) -> List[Boolean]:
        pass

    @abstractmethod
    def _property_constraint_implementation(self) -> Boolean:
        pass

    def __init__(
            self,
            checked_input: Input,
            checked_history: List[str],
            generate_preconditions: bool,
            generate_counterexamples: bool
    ):
        """create a solver for a certain input and checked history"""
        self.input = checked_input
        self.checked_history = checked_history
        self.generate_preconditions = generate_preconditions
        self.generate_counterexamples = generate_counterexamples

        self._solver = z3.Solver()
        self._solver.set("unsat_core", True)
        self._solver.set("core.minimize", True)

        self._pair2label = {}
        self._label2pair = {}
        self._subtree2label = {}
        self._label2subtree = {}
        self._action_variables = {}
        self._exclude_variables = set()
        self._generated_preconditions = set()

        self._add_action_constraints([], self.input.tree)
        self._add_history_constraints(self.checked_history)

    # TODO define a class for results
    def solve(self) -> Dict[str, Any]:
        """
        the main solving routine

        if we failed to find a solution, return empty list
        otherwise, returns a solution to report later
        """
        result = {"generated_preconditions": list(self._generated_preconditions),
                  "counterexamples": [],
                  "strategies": []}

        # a solver that manages case splits, AVATAR style
        case_solver = z3.Solver()
        # a solver that minimizes assumptions in case splits
        minimize_solver = z3.Solver()

        # both should know about initial constraints for the property we're trying
        for constraint in itertools.chain(
                self.input.initial_constraints,
                self._generated_preconditions,
                self._property_initial_constraints()
        ):
            case_solver.add(constraint)
            minimize_solver.add(constraint)

        # there is no point in comparing e.g. p_A > epsilon
        # therefore, partition case splits into real and infinitesimal parts
        reals = set()
        infinitesimals = set()

        while case_solver.check() == z3.sat:
            # an assignment of variables to concrete real values
            model = case_solver.model()

            # we can use this model to decide whether
            # left > right, left = right or left < right
            def split(left, right):
                if model.evaluate(left > right, True):
                    return left > right
                elif model.evaluate(left == right, True):
                    return left == right
                else:
                    return right > left

            # the current case is the conjunction of all known expression comparisons
            case = [
                split(left, right)
                for left, right in itertools.chain(
                    itertools.combinations(reals, 2),
                    itertools.combinations(infinitesimals, 2)
                )
                # no point in providing e.g. 2.0 > 1.0
                if type(left) != float or type(right) != float
            ]
            case = eliminate_consequences(minimize_solver, set(case))
            logging.info(f"current case assumes {case}")

            property_constraint = self._property_constraint(case)
            if self._solver.check(property_constraint, *self._label2pair.keys(), *self._label2subtree.keys()) == z3.sat:
                logging.info("case solved")
                result["strategies"].append(self._extract_strategy(case))

                # we solved this case, now add a conflict to move on
                case_solver.add(disjunction(*(
                    negation(spl) for spl in case
                )))
            else:
                # we need to compare more expressions
                logging.info("no solution, trying case split")

                # track whether we actually found any more
                new_expression = False
                for label in self._solver.unsat_core():
                    # sometimes solver generates garbage for some reason, exclude it
                    if not isinstance(label, z3.BoolRef) or not z3.is_app(label):
                        continue

                    if label in self._label2pair:
                        # `left op right` was in an unsat core
                        left, right, real = self._label2pair[label]
                        # partition reals/infinitesimals
                        add_to = reals if real else infinitesimals

                        for x in (left, right):
                            # exclude utility variables
                            if x in self._exclude_variables:
                                continue
                            # found one we didn't know about yet
                            if x not in add_to:
                                logging.info(f"new expression: {x}")
                                add_to.add(x)
                                new_expression = True

                # we saturated, give up
                if not new_expression:
                    logging.error("no more splits, failed")
                    logging.error(f"here is a case I cannot solve: {case}")

                    if self.generate_counterexamples:
                        # property constraint is now fixed
                        self._solver.add(property_constraint)
                        # we no longer care about unsat cores for expression comparisons,
                        # so just assert it and move along
                        for label in self._label2pair.keys():
                            self._solver.add(label)

                        labels = set(self._label2subtree.keys())
                        for core in minimal_unsat_cores(self._solver, labels):
                            logging.info("counterexample found - property cannot be fulfilled because of:")
                            for label in core:
                                # sometimes solver generates garbage for some reason, exclude it
                                if not isinstance(label, z3.BoolRef) or not z3.is_app(label):
                                    continue

                                if label in self._label2subtree:
                                    subtree = self._label2subtree[label]
                                    players, history = subtree
                                    # TODO do something with the counterexamples?
                                    logging.info(f"- players {players} with history {history}")

                        logging.info("no more counterexamples")

                    if not self.generate_preconditions:
                        return {
                            "generated_preconditions": list(self._generated_preconditions),
                            "counterexamples": [],
                            "strategies": []
                        }
                    else:
                        if len(case) == 0:
                            logging.info(
                                "failed case is implied by preconditions."
                            )
                            return {
                                "generated_preconditions": list(self._generated_preconditions),
                                "counterexamples": [],
                                "strategies": []
                            }
                        self._generated_preconditions.add(disjunction(*(
                            simplify_boolean(negation(constr)) for constr in case
                        )))
                        logging.info(
                            f"here are the generated preconditions: {self._generated_preconditions}"
                        )
                        logging.info(
                            "restarting with a generated set of preconditions"
                        )
                        # TODO control flow here is quite confusing and requires _generated_preconditions
                        # is there a way to do this within the main loop?
                        return self.solve()

        # there are no more possible models, i.e. no more cases to be discharged
        logging.info("no more cases, done")
        return result

    def _add_action_constraints(self, history: List[str], tree: Tree):
        """exactly one action must be taken at this subtree"""
        if isinstance(tree, Leaf):
            return

        assert isinstance(tree, Branch)
        actions = [
            self._action_variable(history, action)
            for action in tree.actions
        ]
        self._solver.add(disjunction(*actions))
        for (left, right) in itertools.combinations(actions, 2):
            self._solver.add(disjunction(negation(left), negation(right)))

        for action, tree in tree.actions.items():
            self._add_action_constraints(history + [action], tree)

    def _add_history_constraints(self, checked_history: List[str]):
        """we only care about this history"""
        for i in range(len(checked_history)):
            self._solver.add(self._action_variable(
                checked_history[:i], checked_history[i]
            ))

    def _property_constraint(self, case: Set[z3.BoolRef]) -> z3.BoolRef:
        """
        create a universally-quantified constraint for a given property of the form
        ```
        forall <input constants>.
            <initial constraints> &&
            self._property_initial_constraints() &&
            <case split> => self._property_constraint_implementation()
        ```
        """
        constraint = self._property_constraint_implementation()
        return self._quantify_constants(implication(
            conjunction(
                *self.input.initial_constraints,
                *self._generated_preconditions,
                *self._property_initial_constraints(),
                *case
            ),
            constraint
        ))

    def _quantify_constants(self, constraint: z3.BoolRef) -> z3.BoolRef:
        """quantify `constraint` with the input constants"""
        if len(self.input.constants) == 0:
            return constraint

        return z3.ForAll(
            [z3.Real(constant) for constant in self.input.constants],
            constraint
        )

    def _action_variable(self, history: List[str], action: str) -> z3.BoolRef:
        """the variable representing taking `action` after `history`"""
        tag = ';'.join(history)
        variable = z3.Bool(f'a[{tag}][{action}]')
        self._action_variables[variable] = (history, action)
        return variable

    def _pair_label(
            self,
            left: Real,
            right: Real,
            real: bool
    ) -> z3.BoolRef:
        """label comparisons for unsat cores"""
        label = self._pair2label.get((left, right))
        if label is None:
            label = z3.Bool(f'l[{left}][{right}]')
            self._pair2label[(left, right)] = label
            # store whether the comparison is real-valued for partition later
            self._label2pair[label] = (left, right, real)

        return label

    def _subtree_label(
            self,
            players: Tuple[str],
            subtree_history: List[str]
    ) -> z3.BoolRef:
        """label subtrees for unsat cores"""
        history = tuple(subtree_history)
        label = self._subtree2label.get((players, history))
        if label is None:
            label = z3.Bool(f'ce[{players}][{history}]')
            self._subtree2label[(players, history)] = label
            self._label2subtree[label] = (players, history)

        return label

    def _extract_strategy(self, case: Set[z3.BoolRef]) -> Dict[str, Any]:
        """Extracting strategies from the solver for the current case split."""
        strategy = {}
        model = self._solver.model()
        for name in model:
            if not isinstance(name, z3.FuncDeclRef):
                continue

            variable = name()
            assert isinstance(variable, z3.BoolRef)
            # Only take action variables for strategies
            if variable in self._action_variables and model[name]:
                history, action = self._action_variables[variable]
                strategy[';'.join(history)] = action

        return {
            "case": [repr(c) for c in case],
            "strategy": strategy
        }


class FeebleImmuneStrategySolver(StrategySolver):
    """solver for weak and weaker immunity"""

    @abstractmethod
    def _compare_utilities(self, utility) -> z3.BoolRef:
        pass

    def _property_constraint_implementation(self) -> z3.BoolRef:
        constraints = []
        for player in self.input.players:
            self._collect_weak_immunity_constraints(
                constraints, player, [], [], self.input.tree
            )
        return conjunction(*constraints)

    def _collect_weak_immunity_constraints(
            self,
            constraints: List[z3.BoolRef],
            player: str,
            player_decisions: List[z3.BoolRef],
            history: List[str],
            tree: Tree
    ):
        # if the player makes player_decisions, then its utility should be more than 0.
        if isinstance(tree, Leaf):
            impl = implication(
                conjunction(*player_decisions),
                self._compare_utilities(tree.utilities[player])
            )
            if self.generate_counterexamples:
                impl = implication(self._subtree_label((player,), history), impl)

            constraints.append(impl)
            return

        # walk the tree and collect player's decisions
        assert isinstance(tree, Branch)
        player_decision = tree.player == player
        for action, child in tree.actions.items():
            action_variable = [self._action_variable(history, action)] \
                if player_decision \
                else []
            self._collect_weak_immunity_constraints(
                constraints,
                player,
                player_decisions + action_variable,
                history + [action],
                child
            )


class WeakImmunityStrategySolver(FeebleImmuneStrategySolver):

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.weak_immunity_constraints

    def _compare_utilities(self, utility) -> z3.BoolRef:
        return Utility.__ge__(utility, ZERO, self._pair_label)


class WeakerImmunityStrategySolver(FeebleImmuneStrategySolver):

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.weaker_immunity_constraints

    def _compare_utilities(self, utility) -> z3.BoolRef:
        real_part = Utility.from_real(utility.real)
        return Utility.__ge__(real_part, ZERO, self._pair_label)


class CollusionResilienceStrategySolver(StrategySolver):
    """solver for collusion resilience"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.collusion_resilience_constraints

    def _property_constraint_implementation(self) -> z3.BoolRef:
        utilities_of_checked_history = self.input.tree.get_utility_of_terminal_history(
            self.checked_history
        )

        constraints = []
        for group_size in range(1, len(self.input.players)):
            for colluding_group in itertools.combinations(self.input.players, group_size):
                old_utility = sum((
                    utilities_of_checked_history[player]
                    for player in colluding_group
                ), start=ZERO)
                self._collect_collusion_resilience_constraints(
                    constraints,
                    old_utility,
                    colluding_group,
                    [],
                    [],
                    self.input.tree
                )

        return conjunction(*constraints)

    def _collect_collusion_resilience_constraints(
            self,
            constraints: List[z3.BoolRef],
            old_utility: Utility,
            colluding_group: Tuple[str],
            nongroup_decisions: List[z3.BoolRef],
            history: List[str],
            tree: Tree
    ):
        # the colluding group should not benefit.
        # players that are not in the colluding group have their strategy "fixed"
        # that is the strategy we are trying to find (so nongroup_decisions is antecedens)
        if isinstance(tree, Leaf):
            colluding_utility = sum((
                tree.utilities[player]
                for player in colluding_group
            ), start=ZERO)
            impl = implication(
                conjunction(*nongroup_decisions),
                Utility.__ge__(old_utility, colluding_utility, self._pair_label)
            )
            if self.generate_counterexamples:
                impl = implication(self._subtree_label(colluding_group, history), impl)

            constraints.append(impl)
            return

        assert isinstance(tree, Branch)
        group_decision = tree.player in colluding_group
        for action, child in tree.actions.items():
            action_variable = [] \
                if group_decision \
                else [self._action_variable(history, action)]
            self._collect_collusion_resilience_constraints(
                constraints,
                old_utility,
                colluding_group,
                nongroup_decisions + action_variable,
                history + [action],
                child
            )


class PracticalityStrategySolver(StrategySolver):
    """solver for practicality"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.practicality_constraints

    def _property_constraint_implementation(self) -> z3.BoolRef:
        left_constraints = []
        right_constraints = []
        utility_variables = []
        self._practicality_constraints(left_constraints, right_constraints, utility_variables, [], self.input.tree)
        return z3.ForAll(
                [
                    var
                    for value in utility_variables
                    for var in (value.real, value.inf)
                ], implication(
                    conjunction(*left_constraints),
                    conjunction(*right_constraints)
                )
        )

    def _utility_variable(self, starting_from: List[str], player: str) -> Utility:
        """create real/infinitesimal variables to represent a utility"""
        # utility varible belongs to a subtree. We tag which subtree by the history where we strat from.
        tag = ''.join(starting_from)
        utility = Utility(
            z3.Real(f'ur[{tag}][{player}]'),
            z3.Real(f'ui[{tag}][{player}]')
        )
        self._exclude_variables.update((utility.real, utility.inf))
        return utility

    def _practicality_constraints(
            self,
            left_constraints: List[z3.BoolRef],
            right_constraints: List[z3.BoolRef],
            variables: List[Utility],
            history: List[str],
            tree: Tree
    ):
        """
        adds the practicality constraints to the list constraints.
        tree is the current subtree.
        history is how we got to the subtree.
        """
        if isinstance(tree, Leaf):
            for player in self.input.players:
                variables.append(self._utility_variable(history, player))
                left_constraints.append(Utility.__eq__(self._utility_variable(history, player), tree.utilities[player], self._pair_label))
            return

        assert isinstance(tree, Branch)

        for action in tree.actions:
            utilties_propagate = []
            for player in self.input.players:
                utilties_propagate.append(Utility.__eq__(self._utility_variable(history, player), self._utility_variable(history + [action], player)))
                variables.append(self._utility_variable(history, player))
            impl = implication(self._action_variable(history, action), conjunction(*utilties_propagate))
            left_constraints.append(impl)
            right_constraints.append(Utility.__ge__(self._utility_variable(history, tree.player), self._utility_variable(history + [action], tree.player)))

        maximal_utility_constraints = []
        for action in tree.actions:
            maximal_utility_constraints.append(Utility.__eq__(self._utility_variable(history, tree.player),
                                                              self._utility_variable(history + [action], tree.player)))
        right_constraints.append(disjunction(*maximal_utility_constraints))

        action_choose_maximal = []
        for action in tree.actions:
            implication(Utility.__eq__(self._utility_variable(history, tree.player),
                                       self._utility_variable(history + [action], tree.player)),
                        self._action_variable(history, action))
        right_constraints.append(disjunction(*action_choose_maximal))

        for action, child in tree.actions.items():
            self._practicality_constraints(
                left_constraints,
                right_constraints,
                variables,
                history + [action],
                child
            )
