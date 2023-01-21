# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from typing import Dict, List, Tuple
import itertools
import logging

from auxfunz3 import *
from output import SolvingResult, CaseWithStrategy, Counterexample
from utility import Utility, ZERO
from input import Tree, Leaf, Branch, Input


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

    def solve(self) -> SolvingResult:
        """
        the main solving routine

        if we failed to find a solution, return empty list
        otherwise, returns a solution to report later
        """
        result = SolvingResult(self._generated_preconditions)

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
            logging.info(f"current case assumes {case if case else 'nothing'}")

            property_constraint = self._property_constraint(case)
            if self._solver.check(property_constraint, *self._label2pair.keys(), *self._label2subtree.keys()) == z3.sat:
                logging.info("case solved")
                result.strategies.append(self._extract_strategy(case))

                # we solved this case, now add a conflict to move on
                case_solver.add(disjunction(*(
                    negation(spl) for spl in case
                )))
            else:
                # we need to compare more expressions
                logging.info("no solution, trying case split")

                # track whether we actually found any more
                new_expression = False
                for label_expr in self._solver.unsat_core():
                    # sometimes solver generates garbage for some reason, exclude it
                    if not isinstance(label_expr, z3.BoolRef) or not z3.is_app(label_expr):
                        continue

                    if label_expr in self._label2pair:
                        # `left op right` was in an unsat core
                        left, right, real = self._label2pair[label_expr]
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
                    logging.error(f"here is a case I cannot solve: {case}" if case
                                  else "failed with existing initial constraints")

                    if self.generate_counterexamples:
                        # property constraint is now fixed
                        self._solver.add(property_constraint)
                        # we no longer care about unsat cores for expression comparisons,
                        # so just assert it and move along
                        for label_expr in self._label2pair.keys():
                            self._solver.add(label_expr)

                        labels = set(self._label2subtree.keys())
                        for core in minimal_unsat_cores(self._solver, labels):
                            logging.info("counterexample(s) found - property cannot be fulfilled because of:")
                            for label_expr in core:
                                # sometimes solver generates garbage for some reason, exclude it
                                if not isinstance(label_expr, z3.BoolRef) or not z3.is_app(label_expr):
                                    continue

                                if label_expr in self._label2subtree:
                                    counterexample = self._extract_counterexample(label_expr)
                                    logging.info(str(counterexample))
                                    result.counterexamples.append(counterexample)

                        logging.info("no more counterexamples")

                    if not self.generate_preconditions or not len(case):
                        if self.generate_preconditions and not len(case):
                            logging.info(
                                "failed case is implied by preconditions"
                            )

                        result.set_to_fail(self._generated_preconditions)
                        return result

                    else:
                        new_precondition = disjunction(*(
                            simplify_boolean(negation(constr)) for constr in case
                        ))
                        self._generated_preconditions.add(new_precondition)

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
        label_expr = self._pair2label.get((left, right))
        if label_expr is None:
            label_expr = z3.Bool(f'l[{left}][{right}]')
            self._pair2label[(left, right)] = label_expr
            # store whether the comparison is real-valued for partition later
            self._label2pair[label_expr] = (left, right, real)

        return label_expr

    def _subtree_label(
            self,
            players: Tuple[str],
            subtree_history: List[str]
    ) -> z3.BoolRef:
        """label subtrees for unsat cores"""
        history = tuple(subtree_history)
        label_expr = self._subtree2label.get((players, history))
        if label_expr is None:
            label_expr = z3.Bool(f'ce[{players}][{history}]')
            self._subtree2label[(players, history)] = label_expr
            self._label2subtree[label_expr] = (players, history)

        return label_expr

    def _extract_strategy(self, case: Set[z3.BoolRef]) -> CaseWithStrategy:
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

        return CaseWithStrategy(case, strategy)

    def _extract_counterexample(self, label_expr: z3.BoolRef) -> Counterexample:
        players, history = self._label2subtree[label_expr]
        return Counterexample(list(players), list(history))


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
    """solver for weak immunity"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.weak_immunity_constraints

    def _compare_utilities(self, utility) -> z3.BoolRef:
        return Utility.__ge__(utility, ZERO, self._pair_label)


class WeakerImmunityStrategySolver(FeebleImmuneStrategySolver):
    """solver for weaker immunity"""

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
            non_group_decisions: List[z3.BoolRef],
            history: List[str],
            tree: Tree
    ):
        # the colluding group should not benefit
        # players that are not in the colluding group have their strategy "fixed"
        # that is the strategy we are trying to find (so `non_group_decisions` is antecedent)
        if isinstance(tree, Leaf):
            colluding_utility = sum((
                tree.utilities[player]
                for player in colluding_group
            ), start=ZERO)
            impl = implication(
                conjunction(*non_group_decisions),
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
                non_group_decisions + action_variable,
                history + [action],
                child
            )


class PracticalityStrategySolver(StrategySolver):
    """solver for practicality"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.practicality_constraints

    def _property_constraint_implementation(self) -> z3.BoolRef:
        constraints = []
        self._practicality_constraints(constraints, [], self.input.tree)
        return conjunction(*constraints)

    def _utility_variable(self, starting_from: List[str], player: str) -> Utility:
        """create real/infinitesimal variables to represent a utility"""
        # utility variable belongs to a subtree -> we tag which subtree by the history where we start from
        tag = ''.join(starting_from)
        utility = Utility(
            z3.Real(f'ur[{tag}][{player}]'),
            z3.Real(f'ui[{tag}][{player}]')
        )
        self._exclude_variables.update((utility.real, utility.inf))
        return utility

    def _add_utility_constraints(
            self,
            constraints: List[z3.BoolRef],
            player_utilities: Dict[str, Utility],
            history: List[str],
            decisions: List[z3.BoolRef],
            tree: Tree,
            player: str
    ):
        """add constraints to give the semantics of a utility variable"""
        if isinstance(tree, Leaf):
            # experiment
            # TODO cleanup
            equalities = [Utility.__eq__(player_utilities[player], tree.utilities[player], self._pair_label)]
            # equalities = [Utility.__eq__(ut, tree.utilities[player], self._pair_label) for player, ut in
            #              player_utilities.items()]
            # if we take `decisions` to a leaf, the utility variable has a known value
            constraints.append(implication(
                conjunction(*decisions),
                conjunction(*equalities)
            ))
            return

        assert isinstance(tree, Branch)
        for action, child in tree.actions.items():
            self._add_utility_constraints(
                constraints,
                player_utilities,
                history + [action],
                decisions + [self._action_variable(history, action)],
                child,
                player
            )

    def _practicality_constraints(
            self,
            constraints: List[z3.BoolRef],
            history: List[str],
            tree: Tree
    ):
        """
        adds the practicality constraints to the list constraints.
        tree is the current subtree.
        history is how we got to the subtree.
        """
        if isinstance(tree, Leaf):
            return

        assert isinstance(tree, Branch)
        utility_variables = {
            player: self._utility_variable(history, player)
            for player in self.input.players
        }

        utility_constraints = []
        self._add_utility_constraints(
            utility_constraints,
            utility_variables,
            history,
            [],
            tree,
            tree.player
        )

        nash_constraints = []

        # experiment
        player = tree.player
        self._nash_constraints(
            nash_constraints,
            utility_variables[player],
            player,
            history,
            [],
            tree
        )
        # TODO cleanup
        # for player in self.input.players:
        #    self._nash_constraints(
        #        nash_constraints,
        #        utility_variables[player],
        #        player,
        #        history,
        #        [],
        #        tree
        #    )

        constraints.append(z3.ForAll(
            [
                var
                for value in utility_variables.values()
                for var in (value.real, value.inf)
            ],
            implication(
                conjunction(*utility_constraints),
                conjunction(*nash_constraints)
            )
        ))

        for action, child in tree.actions.items():
            self._practicality_constraints(
                constraints,
                history + [action],
                child
            )

    def _nash_constraints(
            self,
            constraints: List[z3.BoolRef],
            old_utility: Utility,
            player: str,
            history: List[str],
            non_player_decisions: List[z3.BoolRef],
            tree: Tree
    ):
        # player should not benefit from deviating in this subtree.
        if isinstance(tree, Leaf):
            deviating_utility = tree.utilities[player]
            impl = implication(
                conjunction(*non_player_decisions),
                Utility.__ge__(old_utility, deviating_utility, self._pair_label)
            )
            if self.generate_counterexamples:
                impl = implication(self._subtree_label((player,), history), impl)

            constraints.append(impl)
            return

        # all the other players have the strategy fixed (non_player_decisions)
        # we collect these decisions for implication above at the Leaf case
        assert isinstance(tree, Branch)
        player_decision = player == tree.player
        for action, child in tree.actions.items():
            action_variable = [] \
                if player_decision \
                else [self._action_variable(history, action)]
            self._nash_constraints(
                constraints,
                old_utility,
                player,
                history + [action],
                non_player_decisions + action_variable,
                child
            )
