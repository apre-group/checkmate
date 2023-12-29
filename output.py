from typing import Set, Dict, List, Any

from z3 import z3

from constants import SecurityProperty, PROPERTY_TO_JSON_KEY, HONEST_HISTORY_JSON_KEY, \
    GENERATED_PRECONDITIONS_JSON_KEY, JOINT_STRATEGIES_JSON_KEY, COUNTEREXAMPLES_JSON_KEY, \
    COUNTEREXAMPLE_ORDERING_JSON_KEY, COUNTEREXAMPLE_STRATEGIES_JSON_KEY, COUNTEREXAMPLE_HISTORIES_JSON_KEY, JOINT_STRATEGY_ORDERING_JSON_KEY, \
    JOINT_STRATEGY_STRATEGY_JSON_KEY, OR_CONSTRAINT_KEY, PROPERTY_TO_STR


class CaseWithStrategy:
    """strategy satisfying analyzed property in given case"""
    ordering_case: Set[z3.BoolRef]
    strategy: Dict[str, str]

    def __init__(self, case: Set[z3.BoolRef], strategy: Dict[str, str]):
        self.ordering_case = case
        self.strategy = strategy

    def __repr__(self):
        strategy = '; '.join([f"{history}->{action}" for history, action in self.strategy.items()])
        return f"{{\n\t\tcase: {self.ordering_case}\n\t\t" \
               f"strategy: {strategy}\n\t}}"

    def to_json(self) -> Dict[str, Any]:
        return {
            JOINT_STRATEGY_ORDERING_JSON_KEY: [str(c) for c in self.ordering_case],
            JOINT_STRATEGY_STRATEGY_JSON_KEY: self.strategy
        }


class Counterexample:
    """counterexample to analyzed property"""
    ordering_case: Set[z3.BoolRef]
    strategies: List[Dict[str, str]]
    histories: List[str]

    def __init__(self,
                 ordering_case: Set[z3.BoolRef],
                 strategies: List[Dict[str, str]],
                 histories: List[str]):
        self.ordering_case = ordering_case
        self.strategies = strategies
        self.histories = histories

    def __repr__(self):
        outstr = f"\n\t\tcase: {self.ordering_case}\n\t\t"
        outstr += f"\n\t\tstrategies:\n\t\t"
        for strat in self.strategies:
            strategy = '; '.join([f"{history}->{action}" for history, action in strat.items()])
            outstr += f"strategy: {strategy}\n\t"
        outstr += f"\n\t\thistories: {self.histories}\n\t\t"
        return outstr

    def to_json(self) -> Dict[str, Any]:
        # adapt to action and other action!
        return {
            COUNTEREXAMPLE_ORDERING_JSON_KEY: [str(c) for c in self.ordering_case],
            COUNTEREXAMPLE_STRATEGIES_JSON_KEY: self.strategies,
            COUNTEREXAMPLE_HISTORIES_JSON_KEY: self.histories
        }

class CaseWithCounterexamples:
    ordering_case = Set[z3.BoolRef]
    counterexamples = List[Counterexample]

    def __init__(self, case: Set[z3.BoolRef], counterexamples: List[Counterexample] = []):
        self.ordering_case = case
        self.counterexamples = counterexamples

    def __repr__(self):
        return f"---- case: {self.ordering_case}\n" \
               f"---- counterexamples: {self.counterexamples}"

class SolvingResult:
    """result of the analysis of one security property"""
    strategies: List[CaseWithStrategy]
    generated_preconditions: Set[z3.BoolRef]
    counterexamples: List[CaseWithCounterexamples]

    def __init__(self):
        self.strategies = []
        self.generated_preconditions = set()
        self.counterexamples = []

    def __repr__(self):
        return f"---- strategies: {self.strategies}\n" \
               f"---- generated_preconditions: {self.generated_preconditions}\n" \
               f"---- counterexamples: {self.counterexamples}"

    def delete_strategies(self):
        self.strategies.clear()

    def to_json(self) -> Dict[str, Any]:
        return {
            JOINT_STRATEGIES_JSON_KEY: [cws.to_json() for cws in self.strategies],
            GENERATED_PRECONDITIONS_JSON_KEY: [str(prc).replace('Or', OR_CONSTRAINT_KEY) for prc in
                                               self.generated_preconditions],
            COUNTEREXAMPLES_JSON_KEY: [ce.to_json() for ce in self.counterexamples]
        }


class AnalysisResult:
    honest_history: List[str]
    property_results: Dict[SecurityProperty, SolvingResult]

    def __init__(self, honest_history: List[str],
                 weak_immunity_result: SolvingResult = None,
                 weaker_immunity_result: SolvingResult = None,
                 collusion_resilience_result: SolvingResult = None,
                 practicality_result: SolvingResult = None):
        self.honest_history = honest_history
        self.property_results = {SecurityProperty.WEAK_IMMUNITY: weak_immunity_result,
                                 SecurityProperty.WEAKER_IMMUNITY: weaker_immunity_result,
                                 SecurityProperty.COLLUSION_RESILIENCE: collusion_resilience_result,
                                 SecurityProperty.PRACTICALITY: practicality_result}

    def __repr__(self):
        results = '\n'.join(
            [f"-- {PROPERTY_TO_STR[prop]}:\n{res}" for prop, res in self.property_results.items() if res])
        return f"honest_history: {self.honest_history}\n" \
               f"property_results:\n{results}"

    def get_property_result(self, security_property: SecurityProperty) -> SolvingResult:
        return self.property_results[security_property]

    def to_json(self) -> Dict[str, Any]:
        result = {HONEST_HISTORY_JSON_KEY: self.honest_history}

        wi_res = self.get_property_result(SecurityProperty.WEAK_IMMUNITY)
        weri_res = self.get_property_result(SecurityProperty.WEAKER_IMMUNITY)
        cr_res = self.get_property_result(SecurityProperty.COLLUSION_RESILIENCE)
        p_res = self.get_property_result(SecurityProperty.PRACTICALITY)

        if wi_res:
            result[PROPERTY_TO_JSON_KEY[SecurityProperty.WEAK_IMMUNITY]] = wi_res.to_json()
        if weri_res:
            result[PROPERTY_TO_JSON_KEY[SecurityProperty.WEAKER_IMMUNITY]] = weri_res.to_json()
        if cr_res:
            result[PROPERTY_TO_JSON_KEY[SecurityProperty.COLLUSION_RESILIENCE]] = cr_res.to_json()
        if p_res:
            result[PROPERTY_TO_JSON_KEY[SecurityProperty.PRACTICALITY]] = p_res.to_json()

        return result
