from dsl import *
import itertools

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
increment_is_zero = False # whether the increment is positive or zero

# define the players as strings, 
# in this template there are players Player1 and Player2
playerss = [f'Player{i}' for i in range(N)]
PLAYERS = players(*playerss)

# define the actions, infinitesimals and constants as strings and name them for convenience, e.g.:
bid_reserved, outbid, bid_same, bid_anything = ACTIONS = actions('bid_reserved', 'outbid', 'bid_same', 'bid_anything')
ADDITIONAL_ACTIONS = set()
alpha, epsilon = INFINITESIMALS = infinitesimals('alpha', 'epsilon')
player_constants = [NameExpr(f'pl{i}')for i in range(N)]
R, increment, bid_0_player_0 = CONSTANTS = constants('R', 'increment', 'bid_0_player_0') 
for player_const in player_constants:
    CONSTANTS.append(player_const)
# R = reserved price
# increment = minimum increment for the auction



def compute_lottery(permutation : List[int]) -> List[Player]:
    return [PLAYERS[permutation[i]] for i in range(N)]

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [R > 0, increment >= 0, alpha > 0, epsilon > 0]
lottery_options_list = []
lottery_options_conjunctions : List[Constraint] = []
for permutation in itertools.permutations(list(range(N))):
    lottery_options_list.append(list(permutation))
    # permutation = (1,2,0) = (B, C, A)
    conj = conjunction(*[player_constants[permutation[i]] == i for i in range(N)])
    lottery_options_conjunctions.append(conj)
    # we append conjuction(pl1 == 0, pl2 == 1, pl0 == 2) 
INITIAL_CONSTRAINTS.append(disjunction(*lottery_options_conjunctions))

# alternative approach: 
# pl0 == 0 or pl0 == 1 or pl0 == 2
# pl1 == 0 or pl1 == 1 or pl1 == 2
# pl2 == 0 or pl2 == 1 or pl2 == 2
# pl0 != pl1 and pl0 != pl2 and pl1 != pl2



# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[HistoryTree] = []
# [HistoryTree([bid_reserved, bid_reserved, bid_reserved])]

# honest utilities can be listed, if modeling used in an interleaving way with CheckMate
HONEST_UTILITIES = [] 


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
    "current_bid" : {},
    "last_bid_index" : {},
    "highest_bidder" : PLAYERS[0],
    "bids_order" : [R, bid_0_player_0]
}
# some player-wise information, e.g.
for i, player in enumerate(PLAYERS):
    if i == 0:
        initial_state["current_bid"][player] = bid_0_player_0
        initial_state["last_bid_index"][player] = 0
    else:
        initial_state["current_bid"][player] = 0
        initial_state["last_bid_index"][player] = -1

# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {"current_bid" : {}, "last_bid_index" : {}, "bids_order" : []}
    # copy the basic data of the state
    state_copy["highest_bidder"] = state["highest_bidder"]
    state_copy["bids_order"] = list(state["bids_order"])
    # copy the player-wise values (if applicable)
    for player in PLAYERS:
        state_copy["current_bid"][player] = state["current_bid"][player]
        state_copy["last_bid_index"][player] = state["last_bid_index"][player]
    return state_copy

def determine_auction_winners(state : Dict, lottery: List[Player]):
    # Convert bids_order to strings for proper comparison
    bids_order_str = [str(bid) for bid in state["bids_order"]]
    
    # Sort by index in bids_order (higher index = higher bid)
    tmp = sorted(state["current_bid"].items(), 
                 key=lambda x: bids_order_str.index(str(x[1])), 
                 reverse=True)
    return [player for player, _ in tmp[:k]], tmp[k][1] if k < N else tmp[-1][1]

# computing the utility for a final state
def compute_utility(state : Dict, lottery: List[Player]) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    auction_winners, price = determine_auction_winners(state, lottery)
    lottery_tickets = 0
    for player in lottery:
        # define the utility of player relative to the state
        if lottery_tickets < m:
            ut[player] = alpha + state["current_bid"][player] - R
            if player not in auction_winners:
                lottery_tickets += 1
        else:
            if player in auction_winners:
                ut[player] = alpha + state["current_bid"][player] - price
            else:
                ut[player] = - epsilon
    return ut




# deciding whether a final state was reached
def is_final(state : Dict, player_index : int) -> bool:
    # return a boolean
    return player_index >= N


# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(player_index : int, state: Dict, increment_zero : bool) -> List[Action]:
    # compute list of available actions and return it
    avalable_actions = [bid_reserved, outbid]
    if increment_zero:
        avalable_actions.append(bid_same)
    if player_index < k:
         # in the state we store this: the ordering of current bids. [R, bid_0_player_0, bid_0_player_1, bid_0_player_2]
        # player3 has a turn. Suppose k = 10
        # instead of bid_anything we have several acions: for bid 
        # - bid_anything1 : [R, bid_1_player_3, bid_0_player_0, bid_0_player_1, bid_0_player_2]
        # - bid_anything2 : [R, bid_0_player_0, bid_2_player_3, bid_0_player_1, bid_0_player_2]
        # - bid_anything3 : [R, bid_0_player_0, bid_0_player_1, bid_4_player_3, bid_0_player_2]

        # the action is called bid_anything_j, where j is the index where we insert the bid in the state["bids_order"]
        for j in range(1,len(state["bids_order"])):
            avalable_actions.append(Action(f"bid_anything_{j}"))
            ADDITIONAL_ACTIONS.add(Action(f"bid_anything_{j}"))
    return avalable_actions



# generate the game tree
def generate_tree(player_index: int, state: Dict, history: str):
    global increment_is_zero
    
    # decide whether a leaf was reached, i.e. whether we are in a final state
    if is_final(state, player_index):
        condition_actions = {}
        # here is where the lottery happens
        for i, permutation in enumerate(lottery_options_list):
            print("history: ", history)
            # print(state["bids_order"])
            # print("lottery: ", compute_lottery(permutation))
            # auction_winners, price = determine_auction_winners(state, compute_lottery(permutation))
            # print("auction winners: ", auction_winners)
            # print("price: ", price)
            # print("utility: ", compute_utility(state, compute_lottery(permutation)))
            condition_actions[lottery_options_conjunctions[i]] = leaf(compute_utility(state, compute_lottery(permutation)))
        return condition(condition_actions)
    else:
        # otherwise, we are at a branch and have to compute which actions in ACTIONS is available right now
        branch_actions = {} # dictionary that contains an available action as key and the tree this action leads to as value
        # compute an available actions
        player = PLAYERS[player_index]

        available_actions : List[Action] = compute_available_actions(player_index, state,increment_is_zero)

        # for each available action at a time, compute its subtree
        for action in available_actions:

            # copy the state and adapt it according to the taken action
            # e.g.:
            state1 = copy_state(state)
            if action == bid_reserved:
                state1["current_bid"][player] = R
            elif action == outbid:
                highest_bid = state["current_bid"][state["highest_bidder"]]
                bid = NameExpr(f"bid_{state['last_bid_index'][player] + 1}_player_{player_index}")
                if increment_is_zero:
                    INITIAL_CONSTRAINTS.append(bid > highest_bid)
                else:
                    INITIAL_CONSTRAINTS.append(bid >= highest_bid + increment)
                state1["current_bid"][player] = bid
                state1["highest_bidder"] = player
                state1["bids_order"].append(bid)
                state1["last_bid_index"][player] = state["last_bid_index"][player] + 1
            elif action == bid_same:
                highest_bid = state["current_bid"][state["highest_bidder"]]
                state1["current_bid"][player] = highest_bid
            elif "bid_anything" in repr(action):
                bid = NameExpr(f"bid_{state['last_bid_index'][player] + 1}_player_{player_index}")
                state1["current_bid"][player] = bid
                highest_bid = state["current_bid"][state["highest_bidder"]]
                INITIAL_CONSTRAINTS.append(bid > R)
                INITIAL_CONSTRAINTS.append(highest_bid >= bid)
                state1["last_bid_index"][player] = state["last_bid_index"][player] + 1
                state1["bids_order"].insert(int(repr(action).split("_")[-1]), bid)
                # in the state we store this: the ordering of current bids. [R, bid_0_player_0, bid_0_player_1, bid_0_player_2]
                # player3 has a turn. Suppose k = 10
                # instead of bid_anything we have several acions: for bid 
                # - bid_anything1 : [R, bid_1_player_3, bid_0_player_0, bid_0_player_1, bid_0_player_2]
                # - bid_anything2 : [R, bid_0_player_0, bid_2_player_3, bid_0_player_1, bid_0_player_2]
                # - bid_anything3 : [R, bid_0_player_0, bid_0_player_1, bid_4_player_3, bid_0_player_2]

            # add available action and tree to the dictionary 
            branch_actions[action] = generate_tree(player_index + 1, state1, history + str(player) + "." + str(action) + ";")
        
        return branch(player, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(1, initial_state, "")
ACTIONS = ACTIONS + list(ADDITIONAL_ACTIONS)

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