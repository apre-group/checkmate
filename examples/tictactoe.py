from dsl import *
import itertools
import re

ps = PLAYERS = players('A', 'B')
LU, LM, LD, CU, CM, CD, RU, RM, RD = ACTIONS = actions("LU", "LM", "LD", "CU", "CM", "CD", "RU", "RM", "RD" )
s, w, l = CONSTANTS = constants('s', 'w', 'l')
INFINITESIMALS = infinitesimals()
INITIAL_CONSTRAINTS = [
    s > 0,
    w > 0,
    w > s + s + s + s + s + s + s + s + s
]
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []


initial_state = {
    "turns" : 0
}
for player in ps:
    initial_state[player] = {}
    initial_state[player]["won"] = False
    initial_state[player]["taken_actions"] = []


honest = ["CM", "RU", "LU", "RD", "RM", "LM", "CU", "CD", "LD"]

won = [[LU, LM, LD], [CU, CM, CD], [RU, RM, RD], [LU, CU, RU], [LM, CM, RM], [LD, CD, RD], [LU, CM, RD], [LD, CM, RU]]

HONEST_HISTORIES = [[Action(a) for a in honest]]





def copy_state(state: Dict) -> Dict:

    new_state = {"turns" : state["turns"]}
    for player in ps:
        new_state[player] = {}
        new_state[player]["won"] = state[player]["won"]
        new_state[player]["taken_actions"] = [elem for elem in state[player]["taken_actions"]]
    return new_state
    

def has_won(actions: List[Action]) -> bool:

    wins = [[LU, LM, LD], [CU, CM, CD], [RU, RM, RD], [LU, CU, RU], [LM, CM, RM], [LD, CD, RD], [LU, CM, RD], [LD, CM, RU]]

    for win in wins:
        if all([choice in actions for choice in win]):
            return True
        
    return False


def compute_utilities(state: Dict, so_won: bool) -> Dict[Player, LExpr]:

    utility = dict()

    if so_won:
        for player in ps:
            if state[player]["won"] == True:
                utility[player] = w
                for i in range(state["turns"]):
                    utility[player] = utility[player] - s
            else:
                utility[player] = -w 
                for i in range(state["turns"]):
                    utility[player] = utility[player] + s

    else:
        for player in ps:
            utility[player] = 0
        
    return utility


def generate_tree(player: Player, state: Dict, history: List) -> Tree:

    if player == PLAYERS[0]:
        other_player = PLAYERS[1]
    else:
        other_player = PLAYERS[0]

    children = dict()


    if len(history) < 9:
        for action in ACTIONS:
            if not action in history:
                new_state = copy_state(state)
                new_state["turns"] = new_state["turns"] + 1
                new_state[player]["taken_actions"].append(action)

                if has_won(new_state[player]["taken_actions"]):
                    new_state[player]["won"] = True
                    child_tree = leaf(compute_utilities(new_state, True))
                else:
                    child_tree = generate_tree(other_player, new_state, history + [action])
                children[action] = child_tree

        tree = branch(player, children)

    else: 
        assert len(history) == 9
        tree = leaf(compute_utilities(state, False))

    return tree




tictactoe_tree = generate_tree(ps[0], initial_state, [])


TREE = tictactoe_tree

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

