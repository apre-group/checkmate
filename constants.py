from enum import Enum
import z3

class SecurityProperty(Enum):
    WEAK_IMMUNITY = 'wi'
    WEAKER_IMMUNITY = 'weri'
    COLLUSION_RESILIENCE = 'cr'
    PRACTICALITY = 'pr'


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
COUNTEREXAMPLE_ORDERING_JSON_KEY = "ordering"
COUNTEREXAMPLE_STRATEGIES_JSON_KEY = "strategies"
COUNTEREXAMPLE_HISTORIES_JSON_KEY = "histories"
JOINT_STRATEGY_ORDERING_JSON_KEY = "ordering"
JOINT_STRATEGY_STRATEGY_JSON_KEY = "strategy"

CONSTRAINT_FUNS = {
    'Or': z3.Or,
    'And': z3.And,
    'Not': z3.Not
}
