from dsl import *
import itertools
import re

ps = PLAYERS = players('W', 'M', 'G', 'B')
MINE, YOURS = ACTIONS = actions("MINE", "YOURS" )
p, f, a, d = CONSTANTS = constants('p', 'f', 'a', 'd')
INFINITESIMALS = infinitesimals()
INITIAL_CONSTRAINTS = [
    p > 0,
    f > 0,
    -a > 0,
    d > 0,
    p - d > 0,
    f - d > 0
]
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []


initial_state = dict()
for player in ps:
    initial_state[player] = {}
    initial_state[player]["desired"] = False
    initial_state[player]["with_partner"] = False
    initial_state[player]["with_friend"] = False
    initial_state[player]["with_antifriend"] = False

honest = ["MINE", "MINE", "MINE", "MINE"]

HONEST_HISTORIES = [[Action(a) for a in honest]]





def copy_state(state: Dict) -> Dict:

    new_state = dict()
    for player in ps:
        new_state[player] = dict()
        for key, value in state[player].items():
            new_state[player][key] = value
    return new_state
    

def compute_utilities(state: Dict) -> Dict[Player, LExpr]:

    utility = dict()

    for i in range(2):
        if state[ps[2*i]]["desired"] != state[ps[2*i + 1]]["desired"]:
            state[ps[2*i]]["with_partner"] = True
            state[ps[2*i + 1]]["with_partner"] = True
        if state[ps[i]]["desired"] == state[ps[i + 2]]["desired"]:
            state[ps[i]]["with_friend"] = True
            state[ps[i+2]]["with_friend"] = True
        if state[ps[i]]["desired"] != state[ps[-(i+1)]]["desired"]:
            state[ps[i]]["with_antifriend"] = True
            state[ps[-(i+1)]]["with_antifriend"] = True
    
    for player in ps:
        if (not state[player]["with_partner"]) and state[player]["with_friend"] and state[player]["with_antifriend"]:
            # possibility 1/2 of being alone
            utility[player] = a
        elif  not state[player]["with_partner"] and  not state[player]["with_friend"] and not state[player]["with_antifriend"]:
            # possibility 2/2 of being alone
            utility[player] = a
        else:
            if state[player]["desired"]:
                utility[player] = d
            else:
                utility[player] = -d
            if state[player]["with_partner"]:
                utility[player] = utility[player] + p
            else:
                if state[player]["with_friend"]:
                    utility[player] = utility[player] + f
                else:
                    assert state[player]["with_antifriend"], state[player]
                    utility[player] = utility[player] - f

    return utility


def generate_tree(state: Dict, history: List[str]) -> Tree:

    children = dict()

    if len(history) < 4:
        player = ps[len(history)]
        for action in ACTIONS:
            new_state = copy_state(state)

            if action.value == "MINE":
                new_state[player]["desired"] = True

            child_tree = generate_tree(new_state, history + [action])
            children[action] = child_tree

        tree = branch(player, children)

    else: 
        assert len(history) == 4
        tree = leaf(compute_utilities(state))

    return tree




ebos_tree = generate_tree(initial_state, [])


TREE = ebos_tree

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

