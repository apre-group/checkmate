from typing import Set, Dict, List, Any, Union

from z3 import z3

from constants import SecurityProperty, PROPERTY_TO_JSON_KEY, HONEST_HISTORY_JSON_KEY, \
    GENERATED_PRECONDITIONS_JSON_KEY, JOINT_STRATEGIES_JSON_KEY, COUNTEREXAMPLES_JSON_KEY, \
    COUNTEREXAMPLE_PLAYERS_JSON_KEY, COUNTEREXAMPLE_TERMINAL_HISTORY_JSON_KEY, JOINT_STRATEGY_ORDERING_JSON_KEY, \
    JOINT_STRATEGY_STRATEGY_JSON_KEY, OR_CONSTRAINT_KEY


class CaseWithStrategy:
    """strategy satisfying analyzed property in given case"""
    ordering_case: Set[z3.BoolRef]
    strategy: Dict[str, str]

    def __init__(self, case: Set[z3.BoolRef], strategy: Dict[str, str]):
        self.ordering_case = case
        self.strategy = strategy

    def to_json(self) -> Dict[str, Any]:
        return {
            JOINT_STRATEGY_ORDERING_JSON_KEY: [str(c) for c in self.ordering_case],
            JOINT_STRATEGY_STRATEGY_JSON_KEY: self.strategy
        }


class Counterexample:
    """counterexample to analyzed property"""
    players: List[str]
    terminal_history = List[str]

    def __init__(self, players: List[str], terminal_history: List[str]):
        self.players = players
        self.terminal_history = terminal_history

    def __repr__(self):
        return f"- players {self.players} with history {self.terminal_history}"

    def to_json(self) -> Dict[str, Any]:
        return {
            COUNTEREXAMPLE_PLAYERS_JSON_KEY: self.players,
            COUNTEREXAMPLE_TERMINAL_HISTORY_JSON_KEY: self.terminal_history
        }


class SolvingResult:
    """result of the analysis of one security property"""
    strategies: List[CaseWithStrategy]
    generated_preconditions: Set[z3.BoolRef]
    counterexamples: List[Counterexample]

    def __init__(self):
        self.strategies = []
        self.generated_preconditions = set()
        self.counterexamples = []

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
