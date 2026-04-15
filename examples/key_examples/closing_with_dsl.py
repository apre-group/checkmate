# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
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
C_h, C_c, H, D, I,S, P, NP, Uplus ,Uminus, AG = ACTIONS = actions('C_h', 'C_c', 'H', 'D', 'I',"S", 'P','NP', 'Uplus','Uminus','AG')
epsilon, alpha,rho = INFINITESIMALS = infinitesimals('epsilon', 'alpha','rho')
a, b,f,d_A,d_B,c_A,c_B,p_A,p_B = CONSTANTS = constants('a', 'b','f','d_A','d_B','c_A','c_B','p_A','p_B')

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [a > 0, b>0, d_A> 0, d_B>0, f>0, c_A>0, c_B>0, p_A >0, p_B>0, epsilon>0, alpha>0, rho>0, a >= d_B,
    b >= d_A, a >= p_B, b >= p_A, b >= c_A, a>= c_B, alpha > epsilon, epsilon > rho]

# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = [a >= f, b >= f]
WEAKER_IMMUNITY_CONSTRAINTS = [a >= f, b >= f]
COLLUSION_RESILIENCE_CONSTRAINTS = [a - p_B + d_A >= f, b - p_A + d_B >= f]
PRACTICALITY_CONSTRAINTS = [a - p_B + d_A >= f, b - p_A + d_B >= f, c_A != p_A, c_B != p_B]

#define the list of honest histories, as a list of lists of actions
# e.g. one honest history: Action1, Action2, Action3
HONEST_HISTORIES : List[List[Action]] = [[C_h, S], [H]]


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
}
# some player-wise information, e.g.
for player in PLAYERS:
    initial_state[player] = {}
    initial_state[player]["closed_unilaterally"] = None # if yes, then value by which they tried to enrich themselves, 0 if honest
    initial_state[player]["published_revocation"] = None
    initial_state[player]["collaborative_attempt"] = None # if yes, then value by which they tried to enrich themselves, 0 if honest
    initial_state[player]["signed_collab_closing"] = None
    initial_state[player]["ignored_to_close"] = False
    initial_state[player]["proposed_update"] = None # if yes, then value by which current balance of player changes
    initial_state[player]["agreed_to_update"] = False

initial_state[A]["balance"] = a
initial_state[B]["balance"] = b

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
        state_copy[player]["closed_unilaterally"] = state[player]["closed_unilaterally"] # if yes, then value by which they tried to enrich themselves, 0 if honest
        state_copy[player]["published_revocation"] = state[player]["published_revocation"]
        state_copy[player]["collaborative_attempt"] = state[player]["collaborative_attempt"]
        state_copy[player]["signed_collab_closing"] = state[player]["signed_collab_closing"]
        state_copy[player]["ignored_to_close"] = state[player]["ignored_to_close"]
        state_copy[player]["proposed_update"] = state[player]["proposed_update"]
        state_copy[player]["agreed_to_update"] = state[player]["agreed_to_update"]
        state_copy[player]["balance"] = state[player]["balance"]
    return state_copy


# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}

    if state[A]["agreed_to_update"] or state[B]["agreed_to_update"]:
        ut[A] = rho
        ut[B] = rho


    for player in PLAYERS:
        other = other_player(player)
        # unilateral closing
        if not (state[player]["closed_unilaterally"] is None) and not state[other]["published_revocation"]:
            ut[player] = ut[player] + state[player]["closed_unilaterally"] + alpha - epsilon
            ut[other] = ut[other] - state[player]["closed_unilaterally"] + alpha
            return ut

        elif  not (state[player]["closed_unilaterally"] is None) and state[other]["published_revocation"]:
            ut[other] = ut[other] + state[player]["balance"] - f + alpha
            ut[player] = - state[player]["balance"]
            return ut

        # collaborative closing
        elif not (state[player]["collaborative_attempt"] is None ) and state[other]["signed_collab_closing"]:
            if player == A:
                ut[player] = ut[player] + state[player]["collaborative_attempt"][0] - state[player]["balance"] + alpha
                ut[other] = ut[other] + state[player]["collaborative_attempt"][1] - state[other]["balance"] + alpha
            if player == B:
                ut[player] = ut[player] + state[player]["collaborative_attempt"][1] - state[player]["balance"] + alpha
                ut[other] = ut[other] + state[player]["collaborative_attempt"][0] - state[other]["balance"] + alpha
            return ut

    assert(state[A]["ignored_to_close"] and state[B]["ignored_to_close"] )
    ut[A] = -state[A]["balance"]
    ut[B] = -state[B]["balance"]

    return ut

# define who the next player is
def other_player(player : Player) -> Player:
    #return a player
    if player == PLAYERS[0]:
        return PLAYERS[1]
    else:
        return PLAYERS[0]


# deciding whether a final state was reached
def is_final(state : Dict):
    # return a boolean

    if state[A]["ignored_to_close"] and state[B]["ignored_to_close"]:
        return True

    for player in PLAYERS:
        other = other_player(player)
        # honest unilateral closing
        if (str(state[other]["closed_unilaterally"]) == "0"):
            return True


        # dishonest unilateral closing
        if not (state[player]["closed_unilaterally"] is None) and not (state[other]["published_revocation"] is None):
            return True

        # collaborative closing
        elif not (state[player]["collaborative_attempt"] is None ) and state[other]["signed_collab_closing"]:
            return True

    return False


# computes subset of ACTIONS that is possible to take at the given point in the game
def compute_available_actions(player : Player, state : Dict, history : str) -> List[Action]:
    # compute list of available actions and return it

    possible_actions = []
    other = other_player(player)

    if not state[other]["closed_unilaterally"] is None:
        return [P,NP]


    possible_actions.append(H)
    possible_actions.append(D)

    if not state[player]["ignored_to_close"]:
        possible_actions.append(I)

    if not (state[other]["collaborative_attempt"] is None):
        possible_actions.append(S)
        if state[player]["proposed_update"] is None:
            possible_actions.append(Uplus)
            possible_actions.append(Uminus)

    if not (state[other]["proposed_update"] is None) and state[player]["agreed_to_update"] is None:
        possible_actions.append(AG)

    if state[player]["collaborative_attempt"] is None:
        possible_actions.append(C_h)
        possible_actions.append(C_c)

    return possible_actions


# generate the game tree
def generate_tree(player: Player, state: Dict, history: str):
    # print(history)
    # print(state)

    # decide whether a leaf was reached, i.e. whether we are in a final state
    if is_final(state):
        # if we are in a leaf we compute the utility and return
        return leaf(compute_utility(state))
    else:

        other = other_player(player)
        # otherwise, we are at a branch and have to compute which actions in ACTIONS is available right now

        branch_actions = {} # dictionary that contains an available action as key and the tree this action leads to as value

        # compute an available actions
        available_actions : List[Action] = compute_available_actions(player, state, history)

        # for each available action at a time, compute it subtree
        for action in available_actions:

            # copy the state and adapt it according to the taken action
            # e.g.:
            state1 = copy_state(state)
            if action == I:
                state1[player]["ignored_to_close"] = True
            elif action == H:
                state1[player]["closed_unilaterally"] = 0
            elif action == D:
                state1[player]["closed_unilaterally"] = d_A if player == A else d_B
            elif action == P:
                state1[player]["published_revocation"] = True
            elif action == NP:
                state1[player]["published_revocation"] = False
            elif action == C_h:
                state1[other]["ignored_to_close"] = False
                state1[player]["collaborative_attempt"] = (state1[A]["balance"], state1[B]["balance"])
            elif action == C_c:
                state1[other]["ignored_to_close"] = False
                state1[player]["collaborative_attempt"] = (state1[A]["balance"] + c_A, state1[B]["balance"] - c_A) if player == A else (state1[A]["balance"] - c_B, state1[B]["balance"] + c_B)
            elif action == S:
                state1[player]["signed_collab_closing"] = True
            elif action == Uplus:
                state1[other]["ignored_to_close"] = False
                state1[player]["proposed_update"] = (state1[A]["balance"] + p_A, state1[B]["balance"] - p_A)
            elif action == Uminus:
                state1[other]["ignored_to_close"] = False
                state1[player]["proposed_update"] = (state1[A]["balance"] - p_B, state1[B]["balance"] + p_B)
            elif action == AG:
                state1[other]["ignored_to_close"] = False
                state1[player]["agreed_to_update"] = True
                state1[A]["balance"] = state1[other]["proposed_update"][0]
                state1[B]["balance"] = state1[other]["proposed_update"][1]
             # add available action and tree to the dictionary
            branch_actions[action] = generate_tree(other, state1, history + str(player) + "." + str(action) + ";")

        return branch(player, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(PLAYERS[0], initial_state, "")
# print(TREE)

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