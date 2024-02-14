from dsl import *
import itertools
import re

ps = PLAYERS = players('A', 'B', 'C')
C, E = ACTIONS = actions("C", "E" )
inc, a0, b0, c0, plus, minus = CONSTANTS = constants('inc', 'a0', 'b0', 'c0', 'plus', 'minus')
INFINITESIMALS = infinitesimals()
INITIAL_CONSTRAINTS = [
    inc >= 0,
    a0 >= 0,
    b0 >= 0,
    c0 >= 0,
    plus >= 0,
    minus >= 0
]
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []


initial_state = dict()
initial_state[ps[0]] = a0
initial_state[ps[1]] = b0
initial_state[ps[2]] = c0

honest = ["C", "C", "C", "C", "C", "C", "C", "C", "C"]

HONEST_HISTORIES = [[Action(a) for a in honest]]


def copy_state(state: Dict) -> Dict:

    new_state = dict()
    for player in ps:
        new_state[player] = state[player]
    return new_state
    

def generate_tree(state: Dict[Player, LExpr], len_history: int) -> Tree:

    children = dict()
    player = len_history % 3
    next_player = player - 2
    other_player = player - 1


    if len_history < 9:
        children[E] = leaf(state)

        new_state1 = copy_state(state)
        new_state1[ps[next_player]] = new_state1[ps[next_player]] + plus
        new_state1[ps[player]] = new_state1[ps[player]] - minus
        new_state1[ps[other_player]] = new_state1[ps[other_player]] - minus

        children[C] = generate_tree(new_state1, len_history + 1)

        tree = branch(ps[player], children)

    else: 
        assert len_history == 9
        new_state2 = copy_state(state)
        new_state2[ps[0]] = new_state2[ps[0]] + minus + minus - plus
        new_state2[ps[1]] = new_state2[ps[1]] + minus + minus - plus + a0 - b0
        new_state2[ps[2]] = new_state2[ps[2]] + minus + minus - plus + a0 - c0
        tree = leaf(new_state2)

    return tree


centipede_tree = generate_tree(initial_state, 0)

TREE = centipede_tree

finish(
    PLAYERS,
    ACTIONS,
    INFINITESIMALS,
    CONSTANTS,
    INITIAL_CONSTRAINTS,
    WEAK_IMMUNITY_CONSTRAINTS,
    WEAKER_IMMUNITY_CONSTRAINTS,
    COLLUSION_RESILIENCE_CONSTRAINTS,
    PRACTICALITY_CONSTRAINTS,
    HONEST_HISTORIES,
    TREE
)

