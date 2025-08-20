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
A, B = PLAYERS = players('A', 'B')

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
c, d = ACTIONS = actions('c', 'd')
x, y = CONSTANTS = constants('x', 'y')
INFINITESIMALS = []

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = []

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[List[Action]] = [[c, c]]

# honest utilities can be listed, if modeling used in an interleaving way with CheckMate
HONEST_UTILITIES = [] 


# define the initial state as a dictionary
initial_state = {
    A: None,
    B: None,
}

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    import copy
    return copy.deepcopy(state)

# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    return state

# define who the next player is
def next_player(state : Dict) -> Player:
    return A if state[A] is None else B

# deciding whether a final state was reached
def is_final(state : Dict):
    return state[A] is not None and state[B] is not None


# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(player : Player, state : Dict, history : str) -> List[Action]:
    return [c, d]


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

            if player == A:
                if action == c:
                    state1[A] = x
                    state1[B] = x
                else:
                    state1[A] = '???'
            else:
                if action == c:
                    state1[A] = y
                    state1[B] = y
                else:
                    state1[A] = x
                    state1[B] = y

            # add available action and tree to the dictionary 
            branch_actions[action] = generate_tree(next_player(state1), state1, history + str(player) + "." + str(action) + ";")
        
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
    HONEST_UTILITIES,
    TREE
)
