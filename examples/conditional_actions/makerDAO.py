# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
Descibe the protocol and your model here:

Explain the Parameters

ink = the amount of collateral locked in the vault
art = the amount of DAI that is borrowed against the collateral in the vault
lr = the liquidation ratio of the vault
tip = flat reward that the dog gets in DAI
chip = proportional reward that the dog gets, as a fraction of tab
tab = the total DAI the auction must recover total_debt * rate * (1 + chop)
chop = liquidation penalty (multiplier on the total debt)
stability_fee = the fee that the vault owner pays to keep the vault open, as a fraction of the total debt per time unit
prETH = initial price of ETH in DAI (which is 1:1 to dollar)


Design Choices

Assumptions

* L = dog plus clipper
* V = vault owner
* The rate will not change with time, but will be kept at (1 + stability_fee) (instead of being compounded) for simplicity

State

Precedence Choices
"""

# protocol parameters
N = 2 # number of bidders


# define the players as strings, 
# in this template there are players Player1 and Player2
V, L = PLAYERS = players('V', 'L')
for i in range(1, N+1):
    PLAYERS.append(Player('B'+str(i)))

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
frob_close, frob, bark, no_bark, buy_all, buy_some = ACTIONS = actions('frob_close', 'frob', 'bark', 'no_bark', 'buy_all', 'buy_some') # TO DO: fill in the actions
alpha, beta = INFINITESIMALS = infinitesimals('alpha', 'beta')
ink, art, lr, tip, chip, chop, stability_fee, prETH, dink, dart, gas  = CONSTANTS = constants('ink', 'art', 'lr', 'tip', 'chip', 'chop', 'stability_fee', 'prETH', 'dink', 'dart', 'gas')

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [
    ink >= 0,
    art >= 0,
    lr > 1,
    tip >= 0,
    gas < tip, # or comment this out and let checkmate tell us this is a precondition
    chip >= 0,
    chip < 1,
    chop >= 0,
    stability_fee >= 0,
    stability_fee < 1,
    prETH > 0,
    alpha > 0,
    beta > 0,
    ink * prETH > lr * art * (1 + stability_fee),
    (ink + dink) * prETH > lr * (art + dart) * (1 + stability_fee) # dink and dart are such that the vault remains safe
]

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[HistoryTree] = []

# honest utilities can be listed, if modeling used in an interleaving way with CheckMate
HONEST_UTILITIES = [] 


# define the initial state as a dictionary
initial_state = {
    "bids": {i : None for i in range(1, N+1)},
    "debt_left" : True,
    "tab_left" : (art + dart) * (1 + stability_fee) * (1 + chop)
}
# some player-wise information, e.g.
# for player in PLAYERS:
#     initial_state[player] = {}
#     initial_state[player]["amount_to_unlock"] = None

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {}
    # copy the basic data of the state
    state_copy["tab_left"] = state["tab_left"]
    state_copy["debt_left"] = state["debt_left"]
    state_copy["bids"] = {}
    for bidder, bid in state["bids"].items():
        state_copy["bids"][bidder] = bid
    return state_copy


# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    tab = (art + dart) * (1 + stability_fee) * (1 + chop)
    ut[L] = tip * prETH2 + chip * tab - gas * prETH2
    # actual utility of V : if auction closed: (ink + dink - tab/prAuction)*prETH2 + art + dart
    # V had: (ink + dink)*prETH2 - (art + dart)*(stability_fee)
    # actual utility of V: if auction in limbo: art + dart
    # relative utility of V: if auction closed : - tab/prAuction*prETH2 + (art + dart)*(1 + stability_fee) 
    # trying to understand this: - ((art + dart) * (1 + stability_fee) * (1 + chop)* prETH2)/prAuction   + (art + dart)*( 1+ stability_fee) 
    # relative utility of V: if auction in limbo : - (ink + dink)*prETH2 + (art + dart) * (1 + stability_fee)
    if state["debt_left"]:
        # auction in limbo
        ut[V] = - (ink + dink)*prETH2 + (art + dart) * (1 + stability_fee)
    else:
        # auction closed
        ut[V] = - (div_expr(tab, prAuction)) * prETH2 + (art + dart) * (1 + stability_fee) 

    for i in range(1, N+1):
        bidder = i
        if state["bids"][bidder] is None:
            ut[PLAYERS[i+1]] = 0
        else:
            bid = state["bids"][bidder]
            ut[PLAYERS[i+1]] = (div_expr(bid, prAuction)) * (prETH2 - prAuction)
    return ut


# deciding whether a final state was reached
def is_final(state : Dict):
    # return a boolean
    if not state["debt_left"]:
        return True
    for (_, bid) in state["bids"].items():
        if bid is None:
            return False
    return True



# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(state : Dict, history : str) -> List[Action]:
    # compute list of available actions and return it
    return [buy_all, buy_some] 


# generate the game tree
def generate_auction(bidder_index: int, state: Dict, history: str):

    # decide whether a leaf was reached, i.e. whether we are in a final state
    if is_final(state):
        # if we are in a leaf we compute the utility and return
        return leaf(compute_utility(state))
    else:
        # otherwise, we are at a branch and have to compute which actions in ACTIONS is available right now

        branch_actions = {} # dictionary that contains an available action as key and the tree this action leads to as value

        # compute an available actions
        available_actions : List[Action] = compute_available_actions(state, history)

        # for each available action at a time, compute it subtree
        for action in available_actions:

            # copy the state and adapt it according to the taken action
            # e.g.:
            state1 = copy_state(state)
            if action == buy_all:
                state1["bids"][bidder_index] = state1["tab_left"]
                state1["tab_left"] = 0
                state1["debt_left"] = False
                branch_actions[action] = generate_auction(bidder_index + 1, state1, history + str(Player('B'+str(bidder_index))) + "." + str(action) + ";")
            elif action == buy_some:
                bid = NameExpr("bid"+str(bidder_index))
                CONSTANTS.append(bid)
                INITIAL_CONSTRAINTS.append(bid >= 0)
                INITIAL_CONSTRAINTS.append(bid < state["tab_left"])
                state1["bids"][bidder_index] = bid
                state1["tab_left"] = state["tab_left"] - bid
                # debt is not fully covered, so it is still left, but the amount left is reduced
                branch_actions[action] = generate_auction(bidder_index + 1, state1, history + str(Player('B'+str(bidder_index))) + "." + str(action) + ";")

        return branch(Player("B"+str(bidder_index)), branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################

initial_branches = {}
# close the positions with frob_close
ut_close = {V: alpha, L: 0}
for i in range(1, N+1):
    ut_close[Player('B'+str(i))] = 0
initial_branches[frob_close] = leaf(ut_close)

# introduce dink and dart with frob, and then price change
prETH1 = NameExpr("prETH1")
CONSTANTS.append(prETH1)
INITIAL_CONSTRAINTS.append(prETH1>0)
unsafe : Constraint = (ink + dink) * prETH1 < lr * (1 + stability_fee)
safe : Constraint = (ink + dink) * prETH1 >= lr * (1 + stability_fee) 
ut_safe = {V: beta, L: 0}
for i in range(1, N+1):
    ut_safe[Player('B'+str(i))] = 0
branch_actions_unsafe = {}
ut_no_bark = {V: beta, L: 0} # since nobody will ever bark, V gets beta, they are happy with their situation. 
for i in range(1, N+1):
    ut_no_bark[Player('B'+str(i))] = 0
branch_actions_unsafe[no_bark] = leaf(ut_no_bark)

# after bark the price of ETH can change such that 
# the auction is never profitable
prETH2 = NameExpr("prETH2")
CONSTANTS.append(prETH2)
INITIAL_CONSTRAINTS.append(prETH2>0)
prAuction = NameExpr("prAuction")
CONSTANTS.append(prAuction)
INITIAL_CONSTRAINTS.append(prAuction>0)
profitable = prAuction < prETH2
non_profitable = prAuction >= prETH2
# tab = 
ut_non_profitable = {V: (-ink -dink) * prETH2 + (art + dart) , 
                     L: tip * prETH2 + chip * (art + dart) * (1 + stability_fee) * (1 + chop) - gas*prETH2}
for i in range(1, N+1):
    ut_non_profitable[Player('B'+str(i))] = 0


branch_actions_unsafe[bark] = condition({
    non_profitable : leaf(ut_non_profitable), 
    profitable : generate_auction(1, initial_state, "V.frob,unsafe,L.bark,profitable")})


# putting it all together in the frob action
initial_branches[frob] = condition(
    {
    safe : leaf(ut_safe),
    unsafe : branch(L, branch_actions_unsafe)
    }
)

TREE = branch(Player("V"), initial_branches)

# generate the game tree assuming the player listed first in PLAYERS has the first turn

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