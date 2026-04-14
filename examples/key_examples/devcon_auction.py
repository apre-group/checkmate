from dsl import *
import itertools

"""
Descibe the protocol and your model here:

We model the Devcon auction as described in https://notes.ethereum.org/@barnabe/S1eUmr72I

The Devcon auction is a hybrid mechanism combining auction and lottery for ticket allocation. Bidders place bids above a reserve price R. The k highest bidders win auction tickets, while m additional tickets are distributed via lottery among remaining bidders. A random permutation determines payment: auction winners appearing before m lottery winners in the permutation pay the reserve price; others pay the (k+1)-th highest bid. All lottery winners pay the reserve price. The mechanism is incentive-compatible, encouraging truthful bidding. This design balances efficiency (rewarding highest bidders) with fairness (giving everyone above reserve price a chance through the lottery).

Explain the Parameters

The model has the following parameters thet can be adapted to generate different scenarios:
- N: number of players
- k: number of auction winners 
- m: number of lottery winners 
- increment_is_zero: whether the increment is positive or zero 

Design Choices

- The symbolic values representing a bid have the form bid_i_player_j, where i is the index of the bid of player j. E.g. bid_0_player_2 is the first bid of player 2, and bid_1_player_2 is the second bid of player 2.
- We model the permutations of the lottery as symbolic variables pl0, pl1, pl2,... which represent the index of the player in the lottery. E.g. if pl0 == 2, pl1 == 0 and pl2 == 1, this means that player 2 is the first winner of the lottery, player 0 is the second winner of the lottery and player 1 is the third winner of the lottery. We also add constraints (to the set of inital constraints) to ensure that these variables represent a valid permutation.
- We model the benefit of winning a devcon ticket as an infinitesimal alpha, and the opportunity const in case of not winning a devcon ticket as an infinitesimal epsilon. We assume that alpha is positive and epsilon is positive.
- The increment is a non-negative symbolic variable, and we can set it to zero to model the case where there is no minimum increment for the auction.

Assumptions

- Our model does not include the possibility to ignore a bid. A player will always bid something. 
- We do not model repeated bids by the same player, they only bid once. 
- We do not model the possibility to top up a bid if someone outbids you.

State

The state of the game is represented as a dictionary with the following structure:
initial_state = {
    "current_bid" : a dictionary that maps each player to their current bid
    "last_bid_index" : a dictionary that maps each player to the index of their last bid (starting from 0, -1 if no bid was placed)
    "highest_bidder" : the player who currently has the highest bid
    "bids_order" :  an ordered list of current bids, starting with R and then the bids of the players in the order the symbolic variables for bids compare to each other. E.g. [R, bid_0_player_0, bid_0_player_1, bid_0_player_2].
    This is used to determine the winners of the auction at the end of the game, as the k players with the highest bids win. Also, when player is among the fist k players, they can bid anything, so their choice is recorded in the bids order. 
}


Precedence Choices

The bids are given in the player order: Player1, Player2, Player3, ...
We assume Player0 has already placed a bid player_0_bid_0, which is >= R.
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

# define the list of honest histories
# honest behaviour is defined by which players are "in it for the lottery" (they bid reserved) and which players are "in it to win it", meaning they are targeting winning the auction as well
# if a player is in it to win it, and is one of the fist k players, the honest action could also be "bid reserved". 
HONEST_HISTORIES : List[HistoryTree] = []

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
def generate_tree(player_index: int, state: Dict, honest_history_prefix: List[Action], history: str):
    global increment_is_zero
    global HONEST_HISTORIES
    
    # decide whether a leaf was reached, i.e. whether we are in a final state
    if is_final(state, player_index):
        condition_actions = {}
        honest_history_conditions = []
        # here is where the lottery happens
        for i, permutation in enumerate(lottery_options_list):
            condition_actions[lottery_options_conjunctions[i]] = leaf(compute_utility(state, compute_lottery(permutation)))
            honest_history_conditions.append(HistoryTreeCondition(lottery_options_conjunctions[i],HistoryTree([])))
        path = honest_history_prefix + [honest_history_conditions]
        HONEST_HISTORIES.append(HistoryTree(path))
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
            branch_actions[action] = generate_tree(player_index + 1, state1, honest_history_prefix + [action], history + str(player) + "." + str(action) + ";")
        
        return branch(player, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(1, initial_state, [], "")
ACTIONS = ACTIONS + list(ADDITIONAL_ACTIONS)

# print(HONEST_HISTORIES)

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