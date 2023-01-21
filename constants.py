from enum import Enum


class SecurityProperty(Enum):
    WEAK_IMMUNITY = 'WI'
    WEAKER_IMMUNITY = 'WWI'
    COLLUSION_RESILIENCE = 'CR'
    PRACTICALITY = 'P'


PROPERTY_TO_STR = {SecurityProperty.WEAK_IMMUNITY: 'weak immunity',
                   SecurityProperty.WEAKER_IMMUNITY: 'weaker immunity',
                   SecurityProperty.COLLUSION_RESILIENCE: 'collusion resilience',
                   SecurityProperty.PRACTICALITY: 'practicality'}

PROPERTY_TO_JSON_KEY = {SecurityProperty.WEAK_IMMUNITY: 'weak_immunity',
                        SecurityProperty.WEAKER_IMMUNITY: 'weaker_immunity',
                        SecurityProperty.COLLUSION_RESILIENCE: 'collusion_resilience',
                        SecurityProperty.PRACTICALITY: 'practicality'}
ANALYSIS_JSON_KEY = "analysis"
HONEST_HISTORY_JSON_KEY = "honest_history"
JOINT_STRATEGIES_JSON_KEY = "joint_strategies"
GENERATED_PRECONDITIONS_JSON_KEY = "generated_preconditions"
COUNTEREXAMPLES_JSON_KEY = "counterexamples"
COUNTEREXAMPLE_PLAYERS_JSON_KEY = "players"
COUNTEREXAMPLE_TERMINAL_HISTORY_JSON_KEY = "terminal_history"
JOINT_STRATEGY_ORDERING_JSON_KEY = "ordering"
JOINT_STRATEGY_STRATEGY_JSON_KEY = "strategy"

OR_CONSTRAINT_KEY = 'OR'
