from dsl import *

"""
Descibe the protocol and your model here:

Explain the Parameters

Design Choices

Assumptions

State

Precedence Choices
"""


# define the players as strings, 
# in this template there are players Player1 and Player2
PLAYERS = players('Player1', 'Player2')

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
Action1, Action2, Action3 = ACTIONS = actions('Action1', 'Action2', 'Action3')
inf1, inf2 = INFINITESIMALS = infinitesimals('inf1', 'inf2')
cons1, cons2 = CONSTANTS = constants('cons1', 'cons2')

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [cons1 > 0, disjunction(cons2 > 2*cons1, cons2 != -3)]

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[List[Action]] = [[Action1, Action2, Action3]]


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
    "time_orderings": [None for _ in PLAYERS]
}
# some player-wise information, e.g.
for player in PLAYERS:
    initial_state[player] = {}
    initial_state[player]["amount_to_unlock"] = None

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {}
    # copy the basic data of the state
    # e.g.:
    # state1["time_orderings"] = state["time_orderings"][:]
    
    # copy the player-wise values (if applicable)
    for player in PLAYERS:
        state_copy[player] = {}
        # e.g.:
        # state1[player]["amount_to_unlock"] = state[player]["amount_to_unlock"]
    return state_copy


# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    for player in PLAYERS:
        # define the utility of player relative to the state
        # e.g.:
        # if state[player]["contract"] == "unlocked":
        #     ut[player] = ut[player] + inf1 + state[player]["amount_to_unlock"]
        # elif state[player]["contract"] == "expired":
        #     ut[player] = ut[player] - cons1
        pass
    return ut


# define who the next player is
def next_player(state : Dict) -> Player:
    #return a player
    pass


# deciding whether a final state was reached
def is_final(state : Dict):
    # return a boolean
    pass


# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(player : Player, state : Dict, history : str) -> List[Action]:
    # compute list of available actions and return it
    pass


# generate the game tree
def generate_tree(player: Player, state: Dict, history: str):

    # decide whether a leaf was reached, i.e. whether we are in a final state
    if is_final(state):
        # if we are in a leaf we compute the utility and return
        return leaf(compute_utility(state))
    else:
        # otherwise, we are at a branch and have to compute which actions in ACTIONS is available right now

        branch_actions = {} # dictionary that contains an available action as key and the tree this action leads to as value

        # compute an available actions
        available_actions : List[Action] = compute_available_actions(player, state, history)

        # for each available action at a time, compute it subtree
        for action in available_actions:

            # copy the state and adapt it according to the taken action
            # e.g.:
            state1 = copy_state(state)
            state1["some_key"]= "some_value"

            # add available action and tree to the dictionary 
            branch_actions[action] = generate_tree(next_player(state1), state1, history + str(player) + "." + str(action) + ";")
        
        return branch(player, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(PLAYERS[-1], initial_state, "")
print(TREE)

# produce the json model
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