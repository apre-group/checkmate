# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from typing import Dict, List
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

    # a solver that manages case splits, AVATAR style
    _case_solver: z3.Solver
    # a solver that minimizes assumptions in case splits
    _minimize_solver: z3.Solver

    # maintain a bijection from (left, right) expression pairs and Z3 labels
    _pair2label: Dict[Tuple[Real, Real], z3.BoolRef]
    # note extra boolean to partition comparisons into real/infinitesimal
    _label2pair: Dict[z3.BoolRef, Tuple[Real, Real, bool]]

    # maintain a bijection from (player, history) pairs and Z3 labels
    _subtree2label: Dict[Tuple[Tuple[str], Tuple[str], str, str], z3.BoolRef]
    _label2subtree: Dict[z3.BoolRef, Tuple[Tuple[str], Tuple[str], str, str]]

    # mapping from action variables to (history, action) pairs
    _action_variables: Dict[z3.BoolRef, Tuple[List[str], str]]

    # set of variables to exclude from case splits: useful for e.g. utility variables
    _exclude_variables: Set[Real]

    # precomputed property constraint
    _computed_property_constraint: Boolean

    @abstractmethod
    def _property_initial_constraints(self) -> List[Boolean]:
        pass

    @abstractmethod
    def _property_constraint_implementation(self) -> Boolean:
        pass

    @abstractmethod
    def _extract_counterexample_core(self, core: Set[z3.BoolRef]):
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

        self._pair2label = {}
        self._label2pair = {}
        self._subtree2label = {}
        self._label2subtree = {}
        self._action_variables = {}
        self._exclude_variables = set()

        self._minimize_solver = z3.Solver()
        self._case_solver = z3.Solver()
        self._minimize_solver.set('ctrl_c', False)
        # should know about initial constraints for the property we're trying
        initial_constraints = *self.input.initial_constraints, *self._property_initial_constraints()
        self._minimize_solver.add(initial_constraints)
        self._case_solver.add(initial_constraints)

        self._computed_property_constraint = self._property_constraint_implementation()

        self._solver = z3.Solver()
        self._solver.set('ctrl_c', False)
        self._solver.set('core.minimize_partial', True)

        self._add_action_constraints([], self.input.tree)
        self._add_history_constraints(self.checked_history)

    def solve(self) -> SolvingResult:
        """
        the main solving routine

        if we failed to find a solution, return empty list
        otherwise, returns a solution to report later
        """
        result = SolvingResult()

        # there is no point in comparing e.g. p_A > epsilon
        # therefore, partition case splits into real and infinitesimal parts
        reals = set()
        infinitesimals = set()

        while self._case_solver.check() == z3.sat:
            model = self._case_solver.model()
            case = order_according_to_model(model, self._minimize_solver, reals) |\
                order_according_to_model(model, self._minimize_solver, infinitesimals)
            logging.info(f"current case assumes {case if case else 'nothing'}")

            property_constraint = \
                self._property_constraint_for_case(*case, generated_preconditions=result.generated_preconditions)
            check_result = self._solver.check(property_constraint,
                                              *self._label2pair.keys(),
                                              *self._label2subtree.keys())
            if check_result == z3.unknown:
                logging.warning("internal solver returned 'unknown', which shouldn't happen")
                reason = self._solver.reason_unknown()
                logging.warning(f"reason given was: {reason}")
                logging.info("trying again...")
                check_result = self._solver.check(property_constraint,
                                                  *self._label2pair.keys(),
                                                  *self._label2subtree.keys())
                if check_result == z3.unknown:
                    logging.error("solver still says 'unknown', bailing out")
                    assert False

            if check_result == z3.sat:
                case = set(case)
                logging.info("case solved")
                result.strategies.append(self._extract_strategy(case))

                # we solved this case, now add a conflict to move on
                self._case_solver.add(disjunction(*(
                    negation(spl) for spl in case
                )))
            else:
                # we need to compare more expressions
                logging.info("no solution, trying case split")

                # track whether we actually found any more
                new_pair = False

                core = {
                    label_expr
                    for label_expr in self._solver.unsat_core()
                    if isinstance(label_expr, z3.BoolRef) and z3.is_app(label_expr)
                }

                for label_expr in core:
                    if label_expr not in self._label2pair:
                        continue

                    # `left op right` was in an unsat core
                    left, right, real = self._label2pair[label_expr]
                    # partition reals/infinitesimals
                    add_to = reals if real else infinitesimals

                    if (left, right) not in add_to:
                        logging.info(f"new comparison: ({left}, {right})")
                        add_to.add((left, right))
                        add_to.add((right, left))
                        new_pair = True

                # we saturated, give up
                if not new_pair:
                    logging.error("no more splits, failed")
                    logging.error(f"here is a case I cannot solve: {case}" if case
                                  else "failed with existing initial constraints")

                    # delete existing strategies from result because property is not fulfilled
                    result.delete_strategies()

                    if self.generate_counterexamples:
                        # property constraint is now fixed
                        self._solver.add(property_constraint)
                        # we no longer care about unsat cores for expression comparisons,
                        # so just assert it and move along
                        self._solver.add(*self._label2pair.keys())

                        labels = set(self._label2subtree.keys())
                        for core in minimal_unsat_cores(self._solver, labels):
                            logging.info("counterexample(s) found - property cannot be fulfilled because of:")
                            for item in core:
                                print(item)
                                assert self._solver.check(*(core - {item})) == z3.sat
                            counterexample = self._extract_counterexample_core(core)
                            # adapt what we save in the result!
                            result.counterexamples.append(counterexample)

                        logging.info("no more counterexamples")

                    if not self.generate_preconditions or not case:
                        if self.generate_preconditions and not case:
                            logging.info(
                                "failed case is implied by preconditions"
                            )

                        return result

                    else:
                        result.generated_preconditions.add(disjunction(*(
                            simplify_boolean(negation(constr)) for constr in case
                        )))

                        logging.info(
                            f"here are the generated preconditions: {result.generated_preconditions}"
                        )
                        logging.info(
                            "restarting solving routine with the generated set of preconditions"
                        )

                        # reset case and minimizing solver to initial constraints plus generated preconditions
                        self._reset_case_and_minimize_solver(result.generated_preconditions)

        # there are no more possible models, i.e. no more cases to be discharged
        logging.info("no more cases, done")
        return result

    def _reset_case_and_minimize_solver(self, generated_preconditions: Set[z3.BoolRef] = None):
        self._case_solver.reset()
        self._minimize_solver.reset()

        self._minimize_solver.set('ctrl_c', False)

        # both should know about initial constraints for the property we're trying
        for constraint in itertools.chain(
                self.input.initial_constraints,
                generated_preconditions if generated_preconditions else [],
                self._property_initial_constraints()
        ):
            self._case_solver.add(constraint)
            self._minimize_solver.add(constraint)

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

    def _property_constraint_for_case(self, *case: Boolean, generated_preconditions: Set[z3.BoolRef]) -> z3.BoolRef:
        """
        create a universally-quantified constraint for a given property of the form
        ```
        forall <input constants>.
            <initial constraints> &&
            self._property_initial_constraints() &&
            <generated preconditions> &&
            <case split> => self._property_constraint_implementation()
        ```
        """

        return self._quantify_constants(implication(
            conjunction(
                *self.input.initial_constraints,
                *generated_preconditions,
                *self._property_initial_constraints(),
                *case
            ),
            self._computed_property_constraint
        ))

    def _quantify_constants(self, constraint: z3.BoolRef) -> z3.BoolRef:
        """quantify `constraint` with the input constants"""
        if not self.input.constants:
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
            expr: Boolean,
            real: bool
    ) -> Optional[z3.BoolRef]:
        if self._minimize_solver.check(expr) == z3.unsat or self._minimize_solver.check(z3.Not(expr)) == z3.unsat:
            return None

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
            subtree_history: List[str],
            action="",
            other=""
    ) -> z3.BoolRef:
        """label subtrees for unsat cores"""
        history = tuple(subtree_history)
        label_expr = self._subtree2label.get((players, history, action, other))
        if label_expr is None:
            label_expr = z3.Bool(f'ce[{players}][{history}][{action}][{other}]')
            self._subtree2label[(players, history, action, other)] = label_expr
            self._label2subtree[label_expr] = (players, history, action, other)

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
        players, history, action, other_action = self._label2subtree[label_expr]
        return Counterexample(list(players), list(history), action, other_action)


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

    def _extract_counterexample_core(self, core: Set[z3.BoolRef]):
        ces = []
        for label_expr in core:
            counterexample = self._extract_counterexample(label_expr)
            logging.info(f"- {counterexample}")
            ces.append(counterexample)
        return ces

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

    def _extract_counterexample_core(self, core: Set[z3.BoolRef]):
        ces = []
        for label_expr in core:
            counterexample = self._extract_counterexample(label_expr)
            logging.info(f"- {counterexample}")
            ces.append(counterexample)
        return ces

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

    def _extract_counterexample_core(self, core: Set[z3.BoolRef]):
        ces = []
        for label_expr in core:
            counterexample = self._extract_counterexample(label_expr)
            logging.info(f"- {counterexample}")
            ces.append(counterexample)
        return ces

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


class PracticalityStrategySolver2(StrategySolver):
    """solver for practicality - linear (ish) version"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.practicality_constraints

    def _property_constraint_implementation(self) -> z3.BoolRef:
        constraints = []
        self._practicality_constraints(constraints, [], self.input.tree)
        return conjunction(*constraints)

    def _extract_counterexample_core(self, core: Set[z3.BoolRef]):
        ces = []
        for label_expr in core:
            counterexample = self._extract_counterexample(label_expr)
            logging.info(f"- {counterexample}")
            ces.append(counterexample)
        return ces

    def _practicality_constraints(self, constraints: List[Boolean], history: List[str], tree: Tree) -> \
            Dict[str, Dict[Tuple[Real, Real], Boolean]]:
        if isinstance(tree, Leaf):
            return {
                player: {(utility.real, utility.inf): True}
                for player, utility in tree.utilities.items()
            }

        """
        if len(history) < 5:
            print("start", history)
        """

        assert isinstance(tree, Branch)
        utility_map = {}
        for action, child in tree.actions.items():
            utility_map[action] = self._practicality_constraints(constraints, history + [action], child)

        action_variables = {
            action: self._action_variable(history, action)
            for action in tree.actions
        }
        # subtree_label = self._subtree_label((tree.player,), history)

        # if we take an action a and get a certain utility u for it...
        for action, utilities in utility_map.items():
            # (we only care about the current player)
            utilities = utilities[tree.player]
            # for every other a', u'...
            for other, other_utilities in utility_map.items():
                if action == other:
                    continue

                # (we only care about the current player)
                other_utilities = other_utilities[tree.player]

                # (utilities are conditional upon taking actions below us in the tree)
                for utility, condition in utilities.items():
                    utility = Utility(*utility)
                    for other_utility, other_condition in other_utilities.items():
                        subtree_label = self._subtree_label((tree.player, str(condition), str(other_condition)), history, action, other)
                        other_utility = Utility(*other_utility)
                        constraints.append(implication(
                            conjunction(
                                # ...then we know that taking action a means that u >= u'
                                action_variables[action],
                                # (conditionally upon taking certain actions below us)
                                condition,
                                other_condition,
                                subtree_label,
                            ),
                            Utility.__ge__(utility, other_utility, label_fn=self._pair_label),
                        ))

        # build the utility map players->utility->condition
        # the inner map gives a single boolean condition for "player p gets utility u starting from this subtree"
        result = {
            player: {}
            for player in self.input.players
        }
        for action, player_utilities in utility_map.items():
            for player, utilities in player_utilities.items():
                player_result = result[player]
                for utility, condition in utilities.items():
                    condition = conjunction(action_variables[action], condition)
                    if utility in player_result:
                        player_result[utility] = disjunction(condition, player_result[utility])
                    else:
                        player_result[utility] = condition

        #if len(history) == 0:
        #    print(history, result, constraints)
        """
        if len(history) < 5:
            print("end", history)
        """

        return result
