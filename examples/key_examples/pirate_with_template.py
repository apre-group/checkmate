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
A,B,C,D= PLAYERS = players('A', 'B','C','D')

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
y, n = ACTIONS = actions('y', 'n')
INFINITESIMALS = []
a_A, a_B,a_C,a_D,b_B,b_C,b_D,c_C,c_D,g,d = CONSTANTS = constants('a_A', 'a_B','a_C','a_D','b_B','b_C','b_D','c_C','c_D','g','d')

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [d > 0, g > 0, a_A >= 0, a_B >= 0, a_C >= 0, a_D >= 0, b_B >= 0, b_C >= 0, b_D >= 0, c_C >= 0,
                        c_D >= 0, a_A + a_B + a_C + a_D == g, b_B + b_C + b_D == g, c_C + c_D == g]

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[List[Action]] = [[y,y],[y,n,y]]


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
    "current_proposer": PLAYERS[0],
    "final": False
}
# some player-wise information, e.g.
for player in PLAYERS:
    initial_state[player] = {}
    initial_state[player]["agree_to_current_proposal"] = "unknown"

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {}
    # copy the basic data of the state
    # e.g.:
    state_copy["current_proposer"] = state["current_proposer"]
    state_copy["final"] = state["final"]
    
    # copy the player-wise values (if applicable)
    for player in PLAYERS:
        state_copy[player] = {}
        # e.g.:
        state_copy[player]["agree_to_current_proposal"] = state[player]["agree_to_current_proposal"]
    return state_copy


# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    if state["current_proposer"] == A:
        ut[A] = a_A
        ut[B] = a_B
        ut[C] = a_C
        ut[D] = a_D
    else:
        ut[A] = -d 
        if state["current_proposer"] == B:
            ut[B] = b_B
            ut[C] = b_C
            ut[D] = b_D
        else:
            ut[B] = -d 
            assert(state["current_proposer"] == C)
            if state[C]["agree_to_current_proposal"] == "yes" or state[D]["agree_to_current_proposal"] == "yes":
                ut[C] = c_C
                ut[D] = c_D
            else:
                ut[C] = -d 
                ut[D] = g

    return ut


# define who the next player is
def next_player(state : Dict, player: Player) -> Player:
    #return a player
    if player != D:
        ind = PLAYERS.index(player)
        return PLAYERS[ind+1]
    else:
        return state["current_proposer"]



# deciding whether a final state was reached
def is_final(state : Dict):
    # return a boolean
    yes_count = 0
    no_count = 0
    for player in PLAYERS:
        if state[player]["agree_to_current_proposal"] == "yes":
            yes_count = yes_count + 1
        elif state[player]["agree_to_current_proposal"] == "no":
            no_count = no_count + 1

    if yes_count >= 2:
        return True
    elif yes_count == 1 and state["current_proposer"] == C:
        return True
    elif no_count == 2 and state["current_proposer"] == C:
        return True
    
    return False


# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(player : Player, state : Dict, history : str) -> List[Action]:
    # compute list of available actions and return it
    return [y,n]


# generate the game tree
def generate_tree(player: Player, state: Dict, history: str):

    # decide whether a leaf was reached, i.e. whether we are in a final state
    if state["final"]:
        # if we are in a leaf we compute the utility and return
        return leaf(compute_utility(state))
    else:
        # otherwise, we are at a branch and have to compute which actions in ACTIONS is available right now

        branch_actions = {} # dictionary that contains an available action as key and the tree this action leads to as value

        # compute an available actions
        available_actions : List[Action] = compute_available_actions(player, state, history)

        # for each available action at a time, compute it subtree
        for action in available_actions:
            state1 = copy_state(state)
            # copy the state and adapt it according to the taken action
            if action == y:
                state1[player]["agree_to_current_proposal"] = "yes"

            else:
                state1[player]["agree_to_current_proposal"] = "no"

            state1["final"] = is_final(state1) 

            if player == D and not state1["final"]:
                proposer = state1["current_proposer"]
                assert(proposer != D)
                ind = PLAYERS.index(proposer)
                state1["current_proposer"] = PLAYERS[ind+1]
                for p in PLAYERS:
                    state1[p]["agree_to_current_proposal"] = "unknown"

            # add available action and tree to the dictionary 
            branch_actions[action] = generate_tree(next_player(state1, player), state1, history + str(player) + "." + str(action) + ";")
        
        return branch(player, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(PLAYERS[0], initial_state, "")


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
    [],
    TREE
)