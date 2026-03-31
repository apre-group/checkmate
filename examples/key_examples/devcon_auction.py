from dsl import *

"""
Descibe the protocol and your model here:

Explain the Parameters

Design Choices

Assumptions

State

Precedence Choices
"""

# constants of the model, to be adapted to generate different scenarios, e.g. number of players
N = 3 # number of players
k = 1 # number of auction winners
m = 1 # number of lottery winners
increment_is_positive = 1 # whether the increment is positive or zero, set it to 0 if increment = 0.


# define the players as strings, 
# in this template there are players Player1 and Player2
playerss = [f'Player{i}' for i in range(N)]
PLAYERS = players(*playerss)

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
bid_reserved, outbid, bid_same = ACTIONS = actions('bid_reserved', 'outbid', 'bid_same')
alpha, epsilon = INFINITESIMALS = infinitesimals('alpha', 'epsilon')
R, increment = CONSTANTS = constants('R', 'increment')
# R = reserved price
# increment = minimum increment for the auction

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [R > 0, increment >= 0, alpha > 0, epsilon > 0]

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[List[Action]] = [[Action1, Action2, Action3]]

# honest utilities can be listed, if modeling used in an interleaving way with CheckMate
HONEST_UTILITIES = [] 


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
    "current_bid" : {}
}
# some player-wise information, e.g.
for player in PLAYERS:
    initial_state["current_bid"][player] = 0

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {}
    # copy the basic data of the state
    
    # copy the player-wise values (if applicable)
    for player in PLAYERS:
        state_copy["current_bid"][player] = state["current_bid"][player]
    return state_copy

def determine_auction_winners(state : Dict, lottery: List[Player]) -> Tuple[List[Player], LExpr]:
    tmp = sorted(state["current_bid"].items(), key=lambda x: x[1], reverse=True)
    return [player for player, _ in tmp[:k]], tmp[k][1] if k < N else tmp[-1][1]

# computing the utility for a final state
def compute_utility(state : Dict, lottery: List[Player]) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    auction_winners, price = determine_auction_winners(state, lottery)
    lottery_tickets = 0
    for player in lottery:
        # define the utility of player relative to the state
        # e.g.:
        # if state[player]["contract"] == "unlocked":
        #     ut[player] = ut[player] + inf1 + state[player]["amount_to_unlock"]
        # elif state[player]["contract"] == "expired":
        #     ut[player] = ut[player] - cons1
        if lottery_tickets < m:
            ut[player] = alpha + state["current_bid"][player] - R
            if player not in auction_winners:
                lottery_tickets += 1
        else:
            if player in auction_winners:
                ut[player] = alpha + state["current_bid"][player] - price
            else:
                ut[player] = -epsilon
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