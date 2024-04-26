from dsl import *
import itertools
import re

ps = PLAYERS = players('A', 'P1', 'P2', 'P3')
H, L, I, E = ACTIONS = actions("H", "L", "I", "E")
v,  = CONSTANTS = constants('v')
alpha, = INFINITESIMALS = infinitesimals('alpha')
INITIAL_CONSTRAINTS = [v > 0, alpha >0]
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []


initial_state = dict()
initial_state['has_item'] = ps[0]
initial_state['paid_price'] = 0
initial_state['lowest_possible'] = L
for player in ps:
    initial_state[player] = dict()

honest = ["E", "E", "I", "I"]

HONEST_HISTORIES = [[Action(a) for a in honest]]

global COUNT
COUNT = 0


def copy_state(state: Dict) -> Dict:

    new_state = dict()
    new_state['has_item'] = state['has_item']
    new_state['paid_price'] = state['paid_price']
    new_state['lowest_possible'] = state['lowest_possible']
    for player in ps:
        new_state[player] = state[player]
    return new_state
    

def compute_utility(state: Dict, started: bool) -> Dict[Player, LExpr]:
    utilities = dict()
    if not started:
        for player in ps:
            utilities[player] = 0 
    else:
        for player in ps:
            if player == ps[0]:
                if state['has_item'] == player:
                    utilities[player] = - alpha
                else:
                    utilities[player] = - v + state['paid_price'] + alpha
            else:
                if state['has_item'] == player:
                    utilities[player] = v - state['paid_price'] + alpha
                else:
                    utilities[player] = - alpha

    return utilities

def still_possible(lowest: Action, current: Action) -> bool:

    if lowest == L:
        return True
    elif lowest == E and current != L:
        return True
    elif lowest == H and current == H:
        return True
    
    return False


def generate_tree(state: Dict, history: List[str]) -> Tree:
    global COUNT

    children = dict()
    if len(history) < 4:
        player = ps[len(history)]
        for child in ACTIONS:
            new_state = copy_state(state)
            if child == I:
                if history == []:
                    COUNT = COUNT +1 
                    children[child] = leaf(compute_utility(state, False))
                else: 
                    children[child] = generate_tree(new_state, history + ['I'])
            elif still_possible(new_state['lowest_possible'], child):
                if child != E:
                    new_state['lowest_possible'] = child
                    histname = ''
                    for elem in history:
                        histname = histname + elem
                    histname = histname + child.value
                    current_price = NameExpr(f"p_{histname}")
                    CONSTANTS.append(current_price)
                    INITIAL_CONSTRAINTS.append(current_price >= 0)
                    INITIAL_CONSTRAINTS.append(current_price > state['paid_price'])
                    if child == L:
                        INITIAL_CONSTRAINTS.append(v > current_price)
                    elif child == H:
                        INITIAL_CONSTRAINTS.append(current_price > v)
                    new_state['paid_price'] = current_price
                else:
                    if len(history) == 0:
                        new_state["lowest_possible"] = E
                    else:
                        new_state['lowest_possible'] = H
                    new_state['paid_price'] = v


                new_state['has_item'] = player
                children[child] = generate_tree(new_state, history + [child.value])
        COUNT = COUNT + 1        
        tree = branch(player, children)

    else:
        assert len(history) == 4
        COUNT = COUNT + 1
        tree = leaf(compute_utility(state, True))

    return tree


auction_tree = generate_tree(initial_state, [])

#print(COUNT)

TREE = auction_tree

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

