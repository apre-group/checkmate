from dsl import *
import itertools
import re
from typing import Tuple

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

COUNT = 0

initial_state = {
    "turns" : 0
}
for player in ps:
    initial_state[player] = {}
    initial_state[player]["won"] = False
    initial_state[player]["taken_actions"] = []


honest = ["CM", "LU", "RU", "LD", "LM", "RM", "CU", "CD", "RD"]

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


def eval_symmetry(state: Dict) -> List[Action]:

    # for symmetry axis 1: (top left to bottom right)
    symm1 = True
    symm2 = True
    symm3 = True
    symm4 = True
    for player in ps:
        cond11 = (CU in state[player]["taken_actions"]) == (LM in state[player]["taken_actions"]) 
        cond12 = (RU in state[player]["taken_actions"]) == (LD in state[player]["taken_actions"] )
        cond13 = (RM in state[player]["taken_actions"]) == (CD in state[player]["taken_actions"] )
        if not all([cond11, cond12, cond13]):
            symm1 = False
        # symm2 constraint (bottom left to top right)
        cond21 = (LM in state[player]["taken_actions"]) == (CD in state[player]["taken_actions"] )
        cond22 = (LU in state[player]["taken_actions"]) == (RD in state[player]["taken_actions"] )
        cond23 = (CU in state[player]["taken_actions"]) == (RM in state[player]["taken_actions"] )
        if not all([cond21, cond22, cond23]):
            symm2 = False
        # symm3 constraint (center up to center down)
        cond31 = (LU in state[player]["taken_actions"]) == (RU in state[player]["taken_actions"] )
        cond32 = (LM in state[player]["taken_actions"]) == (RM in state[player]["taken_actions"] )
        cond33 = (LD in state[player]["taken_actions"]) == (RD in state[player]["taken_actions"] )
        if not all([cond31, cond32, cond33]):
            symm3 = False
        # symm4 constraint (left middle to right middle)
        cond41 = (LU in state[player]["taken_actions"]) == (LD in state[player]["taken_actions"] )
        cond42 = (CU in state[player]["taken_actions"]) == (CD in state[player]["taken_actions"]) 
        cond43 = (RU in state[player]["taken_actions"]) == (RD in state[player]["taken_actions"]) 
        if not all([cond41, cond42, cond43]):
            symm4 = False

    relevant_actions = [elem for elem in ACTIONS]
    if symm1:
        to_remove = [LM, LD, CD]
        for item in to_remove:
            if item in relevant_actions:
                relevant_actions.remove(item)
    if symm2:
        to_remove = [RM, RD, CD]
        for item in to_remove:
            if item in relevant_actions:
                relevant_actions.remove(item)
    if symm3:
        to_remove = [RU, RM, RD]
        for item in to_remove:
            if item in relevant_actions:
                relevant_actions.remove(item)
    if symm4:
        to_remove = [LD, CD, RD]
        for item in to_remove:
            if item in relevant_actions:
                relevant_actions.remove(item)

    return relevant_actions

def generate_tree(player: Player, state: Dict, history: List) -> Tree:

    global COUNT

    if player == PLAYERS[0]:
        other_player = PLAYERS[1]
    else:
        other_player = PLAYERS[0]

    children = dict()

    poss_actions = eval_symmetry(state)

    if len(history) < 9:
        for action in poss_actions:
            if not action in history:
                new_state = copy_state(state)
                new_state["turns"] = new_state["turns"] + 1
                new_state[player]["taken_actions"].append(action)

                if has_won(new_state[player]["taken_actions"]):
                    new_state[player]["won"] = True
                    COUNT = COUNT +1
                    child_tree = leaf(compute_utilities(new_state, True))
                else:
                    child_tree = generate_tree(other_player, new_state, history + [action])
                children[action] = child_tree
        COUNT = COUNT + 1
        tree = branch(player, children)

    else: 
        assert len(history) == 9
        COUNT = COUNT + 1
        tree = leaf(compute_utilities(state, False))

    return tree



tictactoe_tree = generate_tree(ps[0], initial_state, [])
#print(COUNT)

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
