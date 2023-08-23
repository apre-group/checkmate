# allow type annotations for the current class
# minimum version: 3.7, will be default in future
from __future__ import annotations

from abc import ABCMeta, abstractmethod
from typing import Dict, List, Tuple
import itertools
import logging
from random import shuffle

from auxfunz3 import *
from output import SolvingResult, CaseWithStrategy, Counterexample
from utility import Utility, ZERO
from input import Tree, Leaf, Branch, Input, HistoryTree


class StrategySolver(metaclass=ABCMeta):
    """
    base class for generating strategies from constraints

    subclasses override a few functions and use provided methods
    to implement e.g. weak immunity
    """
    input: Input
    checked_history: HistoryTree
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
    _subtree2label: Dict[Tuple[Tuple[str], Tuple[str], str, str, z3.BoolRef, z3.BoolRef], z3.BoolRef]
    _label2subtree: Dict[z3.BoolRef, Tuple[Tuple[str], Tuple[str], str, str, z3.BoolRef, z3.BoolRef]]

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
    def _extract_counterexample_core(self, core: Set[z3.BoolRef], case, comp_values, model):
        pass

    @abstractmethod
    def _generate_counterexamples(self, core, labels, case, comp_values, model) -> Counterexample:
        pass

    def __init__(
            self,
            checked_input: Input,
            checked_history: HistoryTree,
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

        self._add_action_constraints([], self.input.tree, self._solver)
        self._add_history_constraints(self.checked_history, [])

    def solve(self) -> SolvingResult:
        """
        the main solving routine

        if we failed to find a solution, return empty list
        otherwise, returns a solution to report later
        """ 
        result = SolvingResult()
        result, b = self.case_splitting(True, {True}, [])

        # there are no more possible models, i.e. no more cases to be discharged
        logging.info("no more cases, done")
        return result
    
    def case_splitting(self, new_condition: z3.BoolRef, current_case: Set[z3.BoolRef], comp_values) -> (SolvingResult(), z3.BoolRef):

        result = SolvingResult()

        #check if new condition is implied by init and current_case
        #assert init, current_case, not new_condition
        #init and property -->  

        implication_constraints=self._implied_constraints(new_condition, current_case) 
        implied_result =  self._case_solver.check(implication_constraints)
        #check if new condition is contradictory to init and current_case
        #assert init, current_case, new_condition
        contradiction_constraints=self._contrad_constraints(new_condition, current_case) 
        contrad_result =  self._case_solver.check(contradiction_constraints)

        if implied_result == z3.unsat and new_condition is not True:
            logging.info(f"case {new_condition} implied, the result is unsat")
            #this result is always the result from the parent call
            #unsat no further splits to be considered
            return result, False
        
        if contrad_result == z3.unsat:
            logging.info(f"case {new_condition} impossible, hence trivially satisfied, next case considered")
            return result, True
        elif contrad_result == z3.unsat:
            model = self._case_solver.model(contradiction_constraints)

        case={new_condition}
        for elem in current_case:
            case.add(elem)


        logging.info(f"current case assumes {case}")

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
            result.strategies.append(self._extract_strategy(self._solver, case))
            return result, True
            
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

            core_list = list(core)
            shuffle(core_list)

            for label_expr in core_list:
                if label_expr not in self._label2pair:
                    continue

                # `left op right` was in an unsat core
                left, right, real = self._label2pair[label_expr]
                # partition reals/infinitesimals
                #add_to = reals if real else infinitesimals

                if [left, right] not in comp_values:
                    #call recursively with this split in mind and break for loof here
                    #sat or unsat return value of case_splitting(self, left, right, cases)
                    # unsat breaks the recursion, sat too, only proceed if further cases
                    logging.info(f"new comparison: ({left}, {right})")
                    new_comp = comp_values
                    new_comp.append([left, right])
                    new_comp.append([right, left])

                    output1, sat1 = self.case_splitting(left <= right, case , new_comp)
                    if not sat1:
                        return output1, False
                    else:
                        result.strategies.extend(output1.strategies)
                    
                    output3, sat3 = self.case_splitting(left > right, case , new_comp)
                    if not sat3:
                        return output3, False
                    else:
                        result.strategies.extend(output3.strategies)
                    new_pair = True
                    sat = True
                    break

            # we saturated, give up
            if not new_pair:
                logging.error("no more splits, failed")
                logging.error(f"here is a case I cannot solve: {case}")

                # delete existing strategies from result because property is not fulfilled
                result.delete_strategies()
                sat = False

                if self.generate_counterexamples:
                    # property constraint is now fixed
                    self._solver.add(property_constraint)
                    # we no longer care about unsat cores for expression comparisons,
                    # so just assert it and move along
                    self._solver.add(*self._label2pair.keys())

                    labels = set(self._label2subtree.keys())

                    counterexample = self._generate_counterexamples(core, labels, case, comp_values, model)
                    result.counterexamples.append(counterexample)

                    logging.info("no more counterexamples")

                if not self.generate_preconditions or not case:
                    if self.generate_preconditions and not case:
                        logging.info(
                            "failed case is implied by preconditions"
                        )

                    return result, sat

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



            return result, sat

    
    def _implied_constraints(self, new_condition: z3.BoolRef, current_case: Set[z3.BoolRef]) -> z3.BoolRef:
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
        return conjunction(
                *self.input.initial_constraints,
                *self._property_initial_constraints(),
                *current_case,
                z3.Not(new_condition)
            )

    def _contrad_constraints(self, new_condition: z3.BoolRef, current_case: Set[z3.BoolRef]) -> z3.BoolRef:
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
        return conjunction(
                *self.input.initial_constraints,
                *self._property_initial_constraints(),
                *current_case,
                new_condition
                )

    def _history_constraints_ce(self, hstar: HistoryTree, history: List[str]):
        """computing list of all hstar action variables for counterexample extraction"""
        action_var_list = []
        if len(hstar.children) == 0:
            if hstar.action:
                assert(len(history) > 0) # the history should begin with ''.
                action_var_list.append(self._action_variable(
                    history[1:], hstar.action
                ))
        else:
            for child in hstar.children:
                action_var_list = self._history_constraints_ce(child, history + [hstar.action])
            if hstar.action:
                action_var_list.append(self._action_variable(
                    history, hstar.action
                ))

        return action_var_list

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

    def _add_action_constraints(self, history: List[str], tree: Tree, solver):
        """exactly one action must be taken at this subtree"""
        if isinstance(tree, Leaf):
            return

        assert isinstance(tree, Branch)
        conditions_dict = {}
        for action, child in tree.actions.items():
            conditions_dict[child.condition] = conditions_dict.get(child.condition, [])
            conditions_dict[child.condition].append(self._action_variable(history, action))

        # At least one action per condition
        for cond in conditions_dict:
            solver.add(disjunction(*conditions_dict[cond]))

        # At most one action per condition
        for cond in conditions_dict:
            for (left, right) in itertools.combinations(conditions_dict[cond], 2):
                solver.add(disjunction(negation(left), negation(right)))

        for action, child in tree.actions.items():
            self._add_action_constraints(history + [action], child, solver)


    def _add_history_constraints(self, checked_history: HistoryTree, history: List[str]):
        """we only care about this history"""
        if len(checked_history.children) == 0:
            if checked_history.action:
                assert(len(history) > 0) # the history should begin with ''.
                self._solver.add(self._action_variable(
                    history[1:], checked_history.action
                ))
            return
        else:
            if checked_history.action:
                self._solver.add(self._action_variable(
                    history, checked_history.action
                ))
            for child in checked_history.children:
                self._add_history_constraints(child, history + [checked_history.action])


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
            other="",
            condition=z3.Bool(True),
            other_condition=z3.Bool(True)
    ) -> z3.BoolRef:
        """label subtrees for unsat cores"""
        history = tuple(subtree_history)
        label_expr = self._subtree2label.get((players, history, action, other, condition, other_condition,))
        if label_expr is None:
            label_expr = z3.Bool(f'ce[{players}][{history}][{action}][{other}][{str(condition)}][{str(other_condition)}]')
            self._subtree2label[(players, history, action, other, condition, other_condition)] = label_expr
            self._label2subtree[label_expr] = (players, history, action, other, condition, other_condition)

        return label_expr

    def _list_of_prhist(self, strategy) -> List[str]:
        terminal = False
        hh = strategy[""]
        if strategy.get(hh, None) is None:
            terminal = True
        #think about what do we want as counterexample?
        while not terminal:
            new_hh = []
            terminal = True
            for hist in hh:
                if strategy.get(hist, None) is not None:
                    terminal = False
                    new_hist = []
                    for elem in strategy[hist]:
                        new_hist.append(hist + ";" + elem)
                else:
                    new_hist = [hist]
                new_hh.extend(new_hist)
            hh = new_hh
                  

    def _extract_strategy(self, solver, case: Set[z3.BoolRef], give_history=False) -> Union[CaseWithStrategy, Tuple[CaseWithStrategy, str]]:
        """Extracting strategies from the solver for the current case split."""
        strategy = {}
        model = solver.model()
        for name in model:
            if not isinstance(name, z3.FuncDeclRef):
                continue

            variable = name()
            assert isinstance(variable, z3.BoolRef)
            # Only take action variables for strategies
            if variable in self._action_variables and model[name]:
                history, action = self._action_variables[variable]
                if ';'.join(history) not in strategy.keys():
                    strategy[';'.join(history)] = []
                strategy[';'.join(history)].append(action)
        if give_history:
            return CaseWithStrategy(case, strategy), self._list_of_prstrat(strategy)
        else:
            return CaseWithStrategy(case, strategy)


class FeebleImmuneStrategySolver(StrategySolver):
    """solver for weak and weaker immunity"""

    @abstractmethod
    def _compare_utilities(self, utility) -> z3.BoolRef:
        pass

    def _property_constraint_implementation(self) -> z3.BoolRef:
        constraints = []
        for player in self.input.players:
            self._collect_weak_immunity_constraints(
                constraints, [], player, [], [], self.input.tree
            )
        return conjunction(*constraints)

    def _generate_counterexamples(self, core, labels, case, comp_values, model):
        """collecting all counterexamples for w(er)i, one per unsat core"""
        ces = []
        problematic_cases = set()
        strong_weak_constraint = []
        for core in minimal_unsat_cores(self._solver, labels):
            logging.info("counterexample found - property cannot be fulfilled because of:")
            for item in core:
                assert self._solver.check(*(core - {item})) == z3.sat
            counterexample, conditions = self._extract_counterexample_core(core, case, comp_values, model)
            if len(conditions):
                problematic_cases.update(conditions)
                strong_weak_constraint.append(negation(conjunction(*conditions)))
            
            # adapt what we save in the result!
            ces.append(counterexample)
        
        strong_weak_solver = z3.Solver()
        strong_weak_solver.add(conjunction(*strong_weak_constraint))
        if strong_weak_solver.check() == z3.sat:
            logging.info(f"Property only weakly violated, the problematic scenarios are {str(problematic_cases)}.")
        elif strong_weak_solver.check() == z3.unsat:
            logging.info("Property strongly violated, every scenario is problematic.")
        else:
            logging.info("something went wrong")

        return Counterexample(case, ces, [])

    def _extract_counterexample_core(self, core: Set[z3.BoolRef], case, comp_values, model):
        """generate readable counterexamples one per unsat core"""
        cestrat_output = []
        cestrat = {}
        conditions = []

        setofp = None
        conditions = set()
        for label_expr in core:
            setofp, hist, _action, _other_action, condition, other_condition = self._label2subtree[label_expr]

            if (not condition == True) and (not str(condition) == "And"):
                conditions.add(condition)

            players_in_hist = self.input.get_players_in_hist(self.input.get_tree(), hist)
            for i, elem in enumerate(hist):
                if players_in_hist[i] != setofp[0]:
                    cestrat[";".join(hist[:i])] = elem
                    cestrat_output.append("player "+players_in_hist[i]+" chooses action "+elem+" after history "+str(hist[:i]))
                # do we want the honest conditions too? good example market-entry-conditional    
                # condition_of_action = self.input.get_condition_at_hist(self.input.get_tree(), hist[:i+1])
                # if not condition_of_action == True:
                #    conditions.append(condition_of_action)
                # to track weak vs strong violence of property, check whether there exists a counterexample for all other cases too 
                # after one with a non-trivial condition was found

        assert setofp is not None, "expected non-empty unsat core"
        logging.info(f"- If player {setofp[0]} follows the honest history and the conditions {str(conditions)} are met, {setofp[0]} can be harmed by strategy:")
        for line in cestrat_output:
            logging.info(f"- {line}")
        return cestrat, conditions

    def _collect_weak_immunity_constraints(
            self,
            constraints: List[z3.BoolRef],
            conditions: List[z3.BoolRef],
            player: str,
            player_decisions: List[z3.BoolRef],
            history: List[str],
            tree: Tree
    ):

        # if the player makes player_decisions, then its utility should be more than 0.
        if isinstance(tree, Leaf):
            impl = implication(
                conjunction(*player_decisions, *conditions),
                self._compare_utilities(tree.utilities[player])
            )
            if self.generate_counterexamples:
                impl = implication(self._subtree_label((player,), history, "", "", conjunction(*conditions)), impl)

            constraints.append(impl)
            return

        # walk the tree and collect player's decisions
        assert isinstance(tree, Branch)
        player_decision = tree.player == player
        for action, child in tree.actions.items():
            action_variable = [self._action_variable(history, action)] \
                if player_decision \
                else []
            child_cond = conditions[:]
            if not child.condition == True:
                child_cond.append(child.condition)

            self._collect_weak_immunity_constraints(
                constraints,
                child_cond,
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

        constraints = []
        for group_size in range(1, len(self.input.players)):
            for colluding_group in itertools.combinations(self.input.players, group_size):
                self._collect_collusion_resilience_constraints(
                    constraints,
                    [],
                    colluding_group,
                    [],
                    True,
                    [],
                    self.checked_history,
                    self.input.tree,
                    self.input.tree
                )

        return conjunction(*constraints)

    def _generate_counterexamples(self, core, labels, case, comp_values, model):
        """collecting all counterexamples for cr, one per unsat core"""
        ces = []
        problematic_cases = set()
        strong_weak_constraint = []
        for core in minimal_unsat_cores(self._solver, labels):
            logging.info("counterexample found - property cannot be fulfilled because of:")
            for item in core:
                assert self._solver.check(*(core - {item})) == z3.sat
            counterexample, conditions = self._extract_counterexample_core(core, case, comp_values, model)
            if len(conditions):
                problematic_cases.update(conditions)
                strong_weak_constraint.append(negation(conjunction(*conditions)))

            # adapt what we save in the result!
            ces.append(counterexample)

        strong_weak_solver = z3.Solver()
        strong_weak_solver.add(conjunction(*strong_weak_constraint))
        if strong_weak_solver.check() == z3.sat:
            logging.info(f"Collusion Resilience only weakly violated, the problematic scenarios are {str(problematic_cases)}.")
        elif strong_weak_solver.check() == z3.unsat:
            logging.info("Collusion Resilience strongly violated, every scenario is problematic.")
        else:
            logging.info("something went wrong")

        return Counterexample(case, ces, [])
    

    def _extract_counterexample_core(self, core: Set[z3.BoolRef], case, comp_values, model):
        """generate readable counterexamples one per unsat core"""
        cestrat_output = []
        cestrat = {}

        setofp = None
        conditions = set()
        for label_expr in core:
            setofp, hist, _action, _other_action, condition, other_condition = self._label2subtree[label_expr]
            players_in_hist = self.input.get_players_in_hist(self.input.get_tree(), hist)

            if (not condition == True) and (not str(condition) == "And"):
                conditions.add(condition)
            if not other_condition == True:
                conditions.add(other_condition)
            for i, elem in enumerate(hist):
                if players_in_hist[i] in setofp:
                    cestrat[";".join(hist[:i])] = elem
                    cestrat_output.append("player "+players_in_hist[i]+" chooses action "+elem+" after history "+str(hist[:i]))
                # to track weak vs strong violence of property, check whether there exists a counterexample for all other cases too 
                # after one with a non-trivial condition was found

        logging.info(f"- If conditions {str(conditions)} are met, players {str(setofp[:])} profit from deviating to strategy:")
        for line in cestrat_output:
            logging.info(f"- {line}")
        return cestrat, conditions

    def _collect_collusion_resilience_constraints(
            self,
            constraints: List[z3.BoolRef],
            conditions: List[z3.BoolRef],
            colluding_group: Tuple[str],
            non_group_decisions: List[z3.BoolRef],
            cutting_honest_hist: bool,
            history: List[str],
            honest_histories: HistoryTree,
            corresponding_honest_subtree: Tree,
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

            for honest_cond, old_utility in self.iterate_honest_histories(honest_histories,
                                                                          [],
                                                                          corresponding_honest_subtree):
                honest_utility = sum((
                                        old_utility[player]
                                        for player in colluding_group
                                     ), start=ZERO)
                impl = implication(
                    conjunction(*non_group_decisions,*honest_cond,*conditions),
                    Utility.__ge__(honest_utility, colluding_utility, self._pair_label)
                )
                if self.generate_counterexamples:
                    impl = implication(self._subtree_label(colluding_group, history, "", "", conjunction(*conditions), conjunction(*honest_cond)), impl)

                constraints.append(impl)
            return

        assert isinstance(tree, Branch)
        group_decision = tree.player in colluding_group
        for action, child in tree.actions.items():
            action_variable = [] \
                if group_decision \
                else [self._action_variable(history, action)]

            child_conditions = conditions[:]
            if not child.condition == True:
                child_conditions.append(child.condition)

            if not cutting_honest_hist:
                child_cutting = False
                child_honest_hist = honest_histories
                child_corresponding_honest = corresponding_honest_subtree
            else:
                for hist_child in honest_histories.children:
                    if hist_child.condition == child.condition:
                        if hist_child.action == action: #still along honest history, thus cutting
                            child_cutting = True
                            child_honest_hist = hist_child
                            child_corresponding_honest = corresponding_honest_subtree.actions[action]
                        else:
                            child_cutting = False
                            child_honest_hist = honest_histories
                            child_corresponding_honest = corresponding_honest_subtree

            self._collect_collusion_resilience_constraints(
                constraints,
                child_conditions,
                colluding_group,
                non_group_decisions + action_variable,
                child_cutting,
                history + [action],
                child_honest_hist,
                child_corresponding_honest,
                child
            )

    def iterate_honest_histories(self,
                                 honest_hist: HistoryTree,
                                 collected_cond: List[z3.BoolRef],
                                 tree: Tree) \
                                 -> Generator[Tuple[List[z3.BoolRef],Utility],None,None]:

        if isinstance(tree, Leaf):
            yield collected_cond, tree.utilities

        else:
            assert isinstance(tree,Branch)
            for child in honest_hist.children:
                child_collected_conditions = collected_cond[:]
                if not child.condition == True:
                    child_collected_conditions.append(child.condition)
                yield from self.iterate_honest_histories(child,child_collected_conditions,tree.actions[child.action])



class PracticalityStrategySolver(StrategySolver):
    """solver for practicality - linear (ish) version"""

    def _property_initial_constraints(self) -> List[Boolean]:
        return self.input.practicality_constraints

    def _property_constraint_implementation(self) -> z3.BoolRef:
        constraints = []
        self._practicality_constraints(constraints, [], self.input.tree)
        return conjunction(*constraints)

    def _generate_counterexamples(self, core, labels, case, comp_values, model):
        """generate all counterexamples to pr, which is independent of unsat cores"""
        return self._extract_counterexample_core(core, case, comp_values, model)

    def _pr_case_splitting(self, new_case: z3.BoolRef, current_case: Set[z3.BoolRef], comp_values, ce_solver: z3.Solver)-> (z3.BoolRef, Set[z3.BoolRef]) :
        
        # implication_constraints=self._implied_constraints(new_case, current_case) 
        # implied_result =  self._case_solver.check(implication_constraints)
        # #check if new condition is contradictory to init and current_case
        # #assert init, current_case, new_case
        # contradiction_constraints=self._contrad_constraints(new_case, current_case) 
        # contrad_result =  self._case_solver.check(contradiction_constraints)

        # if implied_result == z3.unsat and new_case is not True:
        #     logging.info(f"case {new_case} implied, the result is unsat")
        #     #this result is always the result from the parent call
        #     #unsat no further splits to be considered, 
        # not so sure about that!
        #     return result, False
        
        # if contrad_result == z3.unsat:
        #     #logging.info(f"case {new_case} impossible, hence trivially satisfied, next case considered")
        #     new_case = negation(new_case)
        

        case={new_case}
        for elem in current_case:
            case.add(elem)
        case.discard(True)

        # if not new_case == True:
        #     logging.info(f"current case assumes {case}")

        property_constraint = \
            self._property_constraint_for_case(*case, generated_preconditions=set())
        check_result = ce_solver.check(property_constraint, *self._label2pair.keys(), *self._label2subtree.keys())

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
            logging.info(f"counterexamples for case {case}")
            return property_constraint, case
            
        else:
            # we need to compare more expressions

            core = {
                label_expr
                for label_expr in self._solver.unsat_core()
                if isinstance(label_expr, z3.BoolRef) and z3.is_app(label_expr)
            }

            core_list = list(core)
            shuffle(core_list)

            for label_expr in core_list:
                if label_expr not in self._label2pair:
                    continue

                # `left op right` was in an unsat core
                left, right, real = self._label2pair[label_expr]
                # partition reals/infinitesimals
                #add_to = reals if real else infinitesimals

                if [left, right] not in comp_values:
                    #call recursively with this split in mind and break for loof here
                    #sat or unsat return value of case_splitting(self, left, right, cases)
                    # unsat breaks the recursion, sat too, only proceed if further cases
                    #logging.info(f"new comparison: ({left}, {right})")
                    new_comp = comp_values
                    new_comp.append([left, right])
                    new_comp.append([right, left])


                    return self._pr_case_splitting(left <= right, case , new_comp, ce_solver)
                    #return  self.case_splitting(left > right, case , new_comp)
                    

            # we didn't find a new case split
            raise Exception("We should not reach this branch, we are in a final case.")

    def _extract_counterexample_core(self, core: Set[z3.BoolRef], case, comp_values, model):
        """generate readable counterexamples by listing all pr histories"""
        ce, case = self._extract_ces(case, comp_values, model)
        # logging.info("counterexample(s) found - property cannot be fulfilled because of:")
        # logging.info(ce)
        return Counterexample(case, [], ce)

    def _isprefix(self, h, subgame):
        for i in range(min(len(h), len(subgame))):
            if h[i] != subgame[i]:
                return False
        return True

    def _maxprefix(self, h: List[str], hstar: HistoryTree):
        prefix = []
        subtree_hstar = hstar.copy() 
        for elem in h:
            children_actions = [child.action for child in subtree_hstar.children]
            if elem not in children_actions:
                break
            else:
                prefix.append(elem)
                i = children_actions.index(elem) #look for correct subHistoryTree
                subtree_hstar = subtree_hstar.children[i].copy()
        return prefix



    def _extract_ces(self, case, comp_values, model):
        subgame = []
        ce = []
        game = self.input.tree
        hstar = self.checked_history
        deleted_branches = []
        labels_in_subgame = self._label2subtree.keys()

        ce_solver = z3.Solver()
        self._add_action_constraints([], self.input.tree, ce_solver)

        #are conditions implemented in the fct already? YES
        property_constraint = \
            self._property_constraint_for_case(*case, generated_preconditions=set()) 
        
        hstar_constraint = conjunction(*self._history_constraints_ce(hstar,[]))
   
        checked_constriant = conjunction(property_constraint, hstar_constraint)
        check_result_with_hstar = ce_solver.check(checked_constriant, *self._label2pair.keys(), *labels_in_subgame)

        #code adapted until here, think about what pr ce means for conditional actions
        while check_result_with_hstar == z3.unsat and isinstance(game, Branch):
            no_more_hist = False
            pr = []
            shortest_h = hstar
            while not no_more_hist:
                property_constraint = \
                    self._property_constraint_for_case(*case, generated_preconditions=set())
                subgame_actions = conjunction(*[self._action_variable(subgame[:i], subgame[i]) for i in range(len(subgame))])
                checked_constriant = conjunction(property_constraint, subgame_actions)
                check_result = ce_solver.check(checked_constriant, *self._label2pair.keys(), *labels_in_subgame)
                if check_result == z3.sat:

                    # hist is now a list of pr strat (all from the same conditional strategy)
                    _strat, hist = self._extract_strategy(ce_solver, set(), True)

                    # for simplicity pick the first history of hist for now
                    histlist_all = hist[0].split(";")

                    histlist = histlist_all[len(subgame):]
                    h = self._maxprefix(histlist, hstar)
                    ph = self.input.get_player_at_hist(game, h)
                    #to be adapted, multiple honest histories to be considered 
                    cond = self.collect_conditions_along_history(histlist)
                    hstar_terminals = self.terminals_that_sat_conditions(hstar, cond)

                    # for simplicity pick the first one now
                    hstar = hstar_terminals[0]

                    ut_hstar = game.get_utility_of_terminal_history(hstar)[ph]

                    ut_histlist = game.get_utility_of_terminal_history(histlist)[ph]

                    #valuation trick to be adapted, no model exisiting in new case split..
                    comparison_real = valuation(ut_hstar.real, model) < valuation(ut_histlist.real, model)
                    comparison_real_eq = valuation(ut_hstar.real, model) == valuation(ut_histlist.real, model)
                    comparison_infinitesimal = valuation(ut_hstar.inf, model) < valuation(ut_histlist.inf, model)
                    if comparison_real or (comparison_real_eq and comparison_infinitesimal):
                        pr.append(histlist)
                        ce.append(subgame + histlist)
                        #add condition
                        logging.info("counterexample found - property cannot be fulfilled because of:")
                        logging.info(subgame + histlist)

                        #shortest_h now HistoryTree, probs h has to become a HistoryTree too
                        #if len(h) < len(shortest_h):
                        if shortest_h.has_subtree(h):
                            shortest_h = h

                    history_actions = []
                    for i, action in enumerate(histlist):
                        history_actions.append(self._action_variable(list(histlist[:i]), action))
                    ce_solver.add(negation(conjunction(*history_actions)))

                elif check_result == z3.unknown:
                    logging.warning("internal solver returned 'unknown', which shouldn't happen")
                    reason = ce_solver.reason_unknown()
                    logging.warning(f"reason given was: {reason}")

                else:
                    new_pair = False
                    #to be removed
                    reals = []
                    infinitesimals = []

                    core = {
                        label_expr
                        for label_expr in ce_solver.unsat_core()
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

                    if not new_pair:
                        no_more_hist = True
                    else:
                        case = order_according_to_model(model, self._minimize_solver, reals) |\
                            order_according_to_model(model, self._minimize_solver, infinitesimals)
                        logging.info(f"current case assumes {case if case else 'nothing'}")
            # to be adapted to HistoryTree
            #subgame shall be the history leading to the counterexample I guess
            if len(pr) == 0:
                shortest_h = [hstar[0]]
            hstar = hstar[:len(shortest_h)]
            subgame = subgame + shortest_h

            # remove all branches after shortest_h, that appear in pr.
            for action in game.actions.keys():
                if any([self._isprefix(prh, shortest_h + [action]) for prh in pr]):
                    deleted_branches.append(shortest_h + [action])
                    ce_solver.add(negation(self._action_variable(shortest_h, action)))

            game = self.input.get_subtree_at_hist(game, shortest_h)
            labels_in_subgame = []
            for key in self._subtree2label.keys():
                h = key[1]
                act = key[2]
                if self._isprefix(h, subgame):
                    if not any([self._isprefix(h, br) for br in deleted_branches]):
                        labels_in_subgame.append(self._subtree2label[key])
            hstar_constraint = conjunction(*[self._action_variable(hstar[:i], hstar[i]) for i in range(len(hstar))])
            checked_constriant = conjunction(property_constraint, hstar_constraint)
            check_result_with_hstar = ce_solver.check(checked_constriant, *self._label2pair.keys(), *labels_in_subgame)
        return ce, case

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
            action: conjunction(self._action_variable(history, action), child.condition)
            for action, child in tree.actions.items()
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
                        other_utility = Utility(*other_utility)
                        if self.generate_counterexamples:
                            subtree_label = self._subtree_label((tree.player,), history, action, other, condition, other_condition,)
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
                        else:
                            constr = implication(
                                conjunction(
                                    # ...then we know that taking action a means that u >= u'
                                    action_variables[action],
                                    # (conditionally upon taking certain actions below us)
                                    condition,
                                    other_condition,
                                ),
                                Utility.__ge__(utility, other_utility, label_fn=self._pair_label),
                            )
                            constraints.append(constr)
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
    