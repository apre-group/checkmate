# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from typing import Any, Dict, List, Set, Tuple, Union
import itertools
import logging
import z3

from auxfunz3 import Real, Boolean, negation, conjunction, disjunction, implication, minimize, simplify_boolean
from utility import Utility, ZERO
from trees import Tree, Leaf, Branch, Input


class StrategySolver(metaclass=ABCMeta):
    """
    base class for generating strategies from constraints

    subclasses override a few functions and use provided methods
    to implement e.g. weak immunity
    """
    input: Input
    _solver: z3.Solver
    _pair2label: Dict[Tuple[Real, Real], z3.FuncDeclRef]
    # note extra boolean to partition comparisons into real/infinitesimal
    _label2pair: Dict[z3.FuncDeclRef, Tuple[Real, Real, bool]]
    _action_variables: Dict[z3.FuncDeclRef, Tuple[List[str], str]]
    _utility_variables: Set[Real]
    _generated_preconditions: Set[z3.BoolRef]

    @abstractmethod
    def _property_initial_constraints(self) -> List[Boolean]:
        pass

    @abstractmethod
    def _property_constraint_implementation(self) -> Boolean:
        pass

    def __init__(self, checked_input: Input, checked_history: List[str]):
        """create a solver for a certain input and checked history"""
        self.input = checked_input
        self.checked_history = checked_history
        self._solver = z3.Solver()
        self._solver.set("unsat_core", True)
        self._solver.set("core.minimize", True)
        # maintain a bijection from (left, right) expression pairs and Z3 labels
        self._pair2label = {}
        self._label2pair = {}
        self._subtree2label = {}
        self._label2subtree = {}
        # mapping from action variables to (history, action) pairs
        self._action_variables = {}
        # the set of utility variables so that we exclude them from case splits
        self._utility_variables = set()
        # the set of generated preconditions in case the game is not secure per se
        self._generated_preconditions = set()

        self._generate_counterexamples = False
        self._old_counterexamples = {}

        self._add_action_constraints([], self.input.tree)
        self._add_history_constraints(self.checked_history)

    def solve(self, generate_preconditions: bool, generate_counterexamples: bool, old_counterexamples=None) -> \
            Dict[str, Any]:
        """
        the main solving routine

        if we failed to find a solution, return empty list
        otherwise, returns a solution to report later
        """
        self._generate_counterexamples = generate_counterexamples
        if not old_counterexamples:
            self._old_counterexamples = {}
        else:
            self._old_counterexamples = old_counterexamples.copy()
        result = {"generated_preconditions": list(self._generated_preconditions),
                  "counterexamples": [],
                  "strategies": []}
        # a solver that manages case splits, AVATAR style
        case_solver = z3.Solver()
        # it should know about initial constraints for the property we're trying
        for constraint in itertools.chain(
                self.input.initial_constraints,
                self._generated_preconditions,
                self._property_initial_constraints()
        ):
            case_solver.add(constraint)

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
            logging.info(f"current case assumes {case}")

            if self._solver.check(self._property_constraint(case)) == z3.sat:
                logging.info("case solved")
                if not self._old_counterexamples:
                    result["strategies"].append(self._extract_strategy(case))
                if generate_counterexamples:
                    result["counterexamples"] = list(self._old_counterexamples.values())

                # we solved this case, now add a conflict to move on
                case_solver.add(disjunction(*(
                    negation(spl) for spl in case
                )))
            else:
                # we need to compare more expressions
                logging.info("no solution, trying case split")

                # track whether we actually found any more
                new_expression = False
                counterexamples = {}
                for item in self._solver.unsat_core():
                    # sometimes solver generates garbage for some reason, exclude it
                    if isinstance(item, z3.BoolRef) and z3.is_app(item):
                        label = item.decl()

                        if label in self._label2pair:
                            # `left op right` was in an unsat core
                            left, right, real = self._label2pair[label]
                            # partition reals/infinitesimals
                            add_to = reals if real else infinitesimals

                            for x in (left, right):
                                # exclude utility variables
                                if x in self._utility_variables:
                                    continue
                                # found one we didn't know about yet
                                if x not in add_to:
                                    logging.info(f"new expression: {x}")
                                    add_to.add(x)
                                    new_expression = True

                        if self._generate_counterexamples and label in self._label2subtree:
                            subtree = self._label2subtree[label]
                            counterexamples[subtree] = _parse_counterexample(self.checked_history, subtree)

                # we saturated, give up
                if not new_expression:
                    logging.error("no more splits, failed")

                    optimizer = z3.Solver()
                    for constraint in itertools.chain(
                            self.input.initial_constraints,
                            self._generated_preconditions,
                            self._property_initial_constraints()
                    ):
                        optimizer.add(constraint)
                    minimized = list(minimize(optimizer, set(case)))

                    logging.error(f"here is a case I cannot solve: {minimized}")

                    if self._generate_counterexamples:
                        for key, ce in counterexamples.items():
                            players = ce["players"]
                            deviation_at = ce["deviation_at"]
                            new_terminal_history = ce["new_terminal_history"]
                            loser = 'group' if isinstance(players, List) else 'player'
                            logging.info(
                                f"counterexample: property not fulfilled for {loser} {players} "
                                f"if players deviate at history {deviation_at}, "
                                f"resulting in history {new_terminal_history}")
                        logging.info(f"old counterexamples: {[key for key in self._old_counterexamples.keys()]}")
                        self._old_counterexamples.update(counterexamples)
                        logging.info(
                            "restarting with a set of old counterexamples"
                        )
                        self._label2subtree = {}
                        self._subtree2label = {}
                        self._label2pair = {}
                        self._pair2label = {}
                        self._solver.reset()
                        self._add_action_constraints([], self.input.tree)
                        self._add_history_constraints(self.checked_history)
                        return self.solve(generate_preconditions, generate_counterexamples, self._old_counterexamples)

                    if not generate_preconditions:
                        return {
                            "generated_preconditions": list(self._generated_preconditions),
                            "counterexamples": counterexamples,
                            "strategies": []
                        }
                    else:
                        if len(minimized) == 0:
                            logging.info(
                                "failed case is implied by preconditions."
                            )
                            return {
                                "generated_preconditions": list(self._generated_preconditions),
                                "counterexamples": counterexamples,
                                "strategies": []
                            }
                        self._generated_preconditions.add(disjunction(*(
                            simplify_boolean(negation(constr)) for constr in minimized
                        )))
                        logging.info(
                            f"here are the generated preconditions: {self._generated_preconditions}"
                        )
                        logging.info(
                            "restarting with a generated set of preconditions"
                        )
                        return self.solve(generate_preconditions, generate_counterexamples)

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

    def _property_constraint(self, case: List[Boolean]) -> z3.BoolRef:
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
        func = z3.Function(f'a[{tag}][{action}]', z3.BoolSort())
        self._action_variables[func] = (history, action)
        variable = func()
        assert isinstance(variable, z3.BoolRef)
        return variable

    def _label(
            self,
            left: Real,
            right: Real,
            real: bool
    ) -> z3.BoolRef:
        """label comparisons for unsat cores"""
        label = self._pair2label.get((left, right))
        if label is None:
            label = z3.Function(f'l[{left}][{right}]', z3.BoolSort())
            self._pair2label[(left, right)] = label
            # store whether the comparison is real-valued for partition later
            self._label2pair[label] = (left, right, real)
            # also assert them here
            expr = label()
            self._solver.assert_and_track(expr, expr)
        else:
            expr = label()

        assert isinstance(expr, z3.BoolRef)
        return expr

    def _subtree_label(
            self,
            players: str,
            subtree_history: List[str]
    ) -> z3.BoolRef:
        history = tuple(subtree_history)
        label = self._subtree2label.get((players, history))
        if label is None:
            if (players, history) not in self._old_counterexamples:
                label = z3.Function(f'ce[{players}][{history}]', z3.BoolSort())
                self._subtree2label[(players, history)] = label
                self._label2subtree[label] = (players, history)
                expr = label()
                self._solver.assert_and_track(expr, expr)
            else:
                expr = z3.Bool(False)
        else:
            expr = label()

        assert isinstance(expr, z3.BoolRef)
        return expr

    def _extract_strategy(self, case: List[z3.BoolRef]) -> Dict[str, Any]:
        """Extracting strategies from the solver for the current case split."""
        strategy = {}
        model = self._solver.model()
        for name in model:
            # Only take action variables for strategies
            if isinstance(name, z3.FuncDeclRef) and name in self._action_variables and model[name]:
                history, action = self._action_variables[name]
                strategy[';'.join(history)] = action

        return {
            "case": [repr(c) for c in case],
            "strategy": strategy
        }


class WeakImmuneStrategySolver(StrategySolver):
    """solver for weak immunity"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.weak_immunity_constraints

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
                Utility.__ge__(tree.utilities[player], ZERO, self._label)
            )
            constraints.append(
                implication(self._subtree_label(player, history), impl) if self._generate_counterexamples else impl)
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
                Utility.__ge__(old_utility, colluding_utility, self._label)
            )
            constraints.append(implication(self._subtree_label(','.join(colluding_group), history),
                                           impl) if self._generate_counterexamples else impl)
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
        constraints = []
        self._practicality_constraints(constraints, [], self.input.tree)
        return conjunction(*constraints)

    def _utility_variable(self, starting_from: List[str], player: str) -> Utility:
        """create real/infinitesimal variables to represent a utility"""
        # utility varible belongs to a subtree. We tag which subtree by the history where we strat from.
        tag = ''.join(starting_from)
        utility = Utility(
            z3.Real(f'ur[{tag}][{player}]'),
            z3.Real(f'ui[{tag}][{player}]')
        )
        self._utility_variables.update((utility.real, utility.inf))
        return utility

    def _define_utility_variable(
            self,
            constraints: List[z3.BoolRef],
            starting_from: List[str],
            player: str,
            tree: Tree
    ) -> Utility:
        """
        define a utility variable for a player starting at a subtree

        a new variable is registered and constraints are added to `constraints`
        """
        variable = self._utility_variable(starting_from, player)
        self._add_utility_constraints(
            constraints,
            variable,
            player,
            starting_from,
            [],
            tree
        )
        return variable

    def _add_utility_constraints(
            self,
            constraints: List[z3.BoolRef],
            variable: Utility,
            player: str,
            history: List[str],
            decisions: List[z3.BoolRef],
            tree: Tree
    ):
        """add constraints to give the semantics of a utility variable"""
        if isinstance(tree, Leaf):
            utility = tree.utilities[player]
            # if we take `decisions` to a leaf, the utility variable has a known value
            constraints.append(implication(
                conjunction(*decisions),
                Utility.__eq__(variable, utility, self._label)
            ))
            return

        assert isinstance(tree, Branch)
        for action, child in tree.actions.items():
            self._add_utility_constraints(
                constraints,
                variable,
                player,
                history + [action],
                decisions + [self._action_variable(history, action)],
                child
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
        utility_constraints = []
        utility_variables = {
            player: self._define_utility_variable(
                utility_constraints,
                history,
                player,
                tree
            )
            for player in self.input.players
        }

        nash_constraints = []
        for player in self.input.players:
            self._nash_constraints(
                nash_constraints,
                utility_variables[player],
                player,
                history,
                [],
                tree
            )

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
            nonplayer_decisions: List[z3.BoolRef],
            tree: Tree
    ):
        # player should not benefit from deviating in this subtree.
        if isinstance(tree, Leaf):
            deviating_utility = tree.utilities[player]
            impl = implication(
                conjunction(*nonplayer_decisions),
                Utility.__ge__(old_utility, deviating_utility, self._label)
            )
            constraints.append(
                implication(self._subtree_label(player, history), impl) if self._generate_counterexamples else impl)
            return

        # all the other players have the strategy fixed (nonplayer_decisions)
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
                nonplayer_decisions + action_variable,
                child
            )


def _parse_counterexample(checked_history: List[str], counterexample_label: Tuple[str, Tuple[str]]) -> \
        Dict[str, Union[str, List[str]]]:
    players = counterexample_label[0]
    history = counterexample_label[1]
    deviation_at = []

    for index in range(0, len(history)):
        if checked_history[index] == history[index]:
            deviation_at.append(checked_history[index])
        else:
            break

    if ',' in players:
        players = players.split(',')

    return {"players": players, "deviation_at": deviation_at, "new_terminal_history": list(history)}