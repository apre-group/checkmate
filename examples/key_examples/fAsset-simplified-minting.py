from dsl import *

"""
Descibe the protocol and your model here:

Explain the Parameters

Design Choices

Assumptions

State

Precedence Choices
"""


M, L, A = PLAYERS = players('M', 'L', 'A')


I, pp, npp, le, lne, burn = ACTIONS = actions('I', 'pp', 'npp', 'le', 'lne', 'burn')
alpha, eps, pi, gas = INFINITESIMALS = infinitesimals('alpha', 'epsilon', 'pi', 'gas')
l, crSafety, lsize, priceBTC, priceFLR, mfee, crf, nBackedAssets, n, amt, cInit, cr, premium = CONSTANTS = constants('l', 'crSafety','lsize', 'priceBTC', 'priceFLR', 'mfee', 'crf', 'nBackedAssets', 'n', 'amt', 'cInit', 'cr', 'premium')

# list your assumptions and design choices as iniital constraints (if applicable),
# the following expressions are supported: +, -, *, /, real numbers, >, >=, <, <=, ==, != (inequality), disjunction(*args) (or)
# e.g.
INITIAL_CONSTRAINTS = [
    priceBTC == 85500,
    priceFLR == 0.01607,
    premium >= 0.2,
    0.5 >= premium,
    cr > 1,
    crSafety > cr,
    cInit > 0,
    lsize == 0.05,
    mfee > 0,
    crf > 0,
    eps > 0,
    alpha > 0,
    pi > 0,
    l > 0,
    gas > 0,
    alpha > 10000 * gas,
    lsize > 0,
    priceBTC > 0,
    priceFLR > 0,
    mfee > 0,
    amt >= 0, # amount to be liquidated cannot be negative
    n > amt, # n is the amount that needs to be liquidated to reach the safety threshold
    ((l * lsize + nBackedAssets) * priceBTC) / cInit > cr, # conditions for minting to be possible
]


# leave the following empty unless you want to debug the protocol
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

#define the list of honest histories
# TO DO
HONEST_HISTORIES  = []

# honest utilities can be listed, if modeling used in an interleaving way with CheckMate
# TO DO
HONEST_UTILITIES = [] 


# define the initial state as a dictionary
initial_state = {
    # probably some general information
    # e.g.:
    "payment_happened": False,
    "payment_proof": False,
    "nonpayment_proof": False,
    "who_proved": M,
    "burning": False,
    "collateral" : cInit,
    "number_backed_assets": nBackedAssets,
    "extra_balance": {M : 0, A : 0, L : 0}
}


# to compute the last missing part, the game tree, the following functions have to be filled in


#################################################################################################################
########################################### tree generation functions ###########################################
#################################################################################################################


# define a deep copy of the state
def copy_state(state : Dict) -> Dict:
    state_copy : Dict = {}
    # copy the basic data of the state
    state_copy["payment_happened"] = state["payment_happened"]
    state_copy["payment_proof"] = state["payment_proof"]
    state_copy["nonpayment_proof"] = state["nonpayment_proof"]
    state_copy["who_proved"] = state["who_proved"]
    state_copy["burning"] = state["burning"]
    state_copy["collateral"] = state["collateral"]
    state_copy["number_backed_assets"] = state["number_backed_assets"]
    
    # copy the player-wise values 
    state_copy["extra_balance"] = {}
    for player in PLAYERS:
        state_copy["extra_balance"][player] = state["extra_balance"][player]

    return state_copy


# computing the utility for a final state
def compute_utility(state : Dict) -> Dict:
    ut : Dict = {player: 0 for player in PLAYERS}
    if state["payment_happened"] and state["payment_proof"]:
        ut[M] = alpha * l
        ut[A] = mfee * l * lsize * priceBTC - l * lsize * (eps + pi)
    elif state["payment_happened"] and not state["payment_proof"] and not state["nonpayment_proof"]:
        ut[M] = (- (1 + mfee) * l * lsize) * priceBTC - crf * l * lsize * priceFLR
        ut[A] = (mfee * l * lsize) * priceBTC
        if state["burning"]:
            ut[A] = ut[A] - l * lsize * priceBTC
        else:
            ut[A] = ut[A] - l * lsize * (crSafety) 
    else: # payment did not happen
        ut[M] = - crf * l * lsize * priceFLR - gas
        if not state["payment_happened"] and state["nonpayment_proof"]:
            ut[A] = crf * l * lsize * priceFLR
        elif not state["payment_happened"] and not state["nonpayment_proof"]:
            if state["burning"]:
                ut[A] = ut[A] - l * lsize * priceBTC - gas
            else:
                ut[A] = ut[A]  - l * lsize * (crSafety)

    if state["payment_proof"] or state["nonpayment_proof"]:
        ut[state["who_proved"]] = ut[state["who_proved"]] - gas

    for player in PLAYERS:
        ut[player] = ut.get(player, 0) + state["extra_balance"][player]

    return ut


def further_actions_A(state : Dict) -> Tree:
    branch_further_actions_A = {}

    # ignore action 
    branch_further_actions_A[I] = leaf(compute_utility(state))

    # provide (non-)payment proof
    if state["payment_happened"]:
        # provide payment proof
        state1 = copy_state(state)
        state1["payment_proof"] = True
        state1["who_proved"] = A
        branch_further_actions_A[pp] = leaf(compute_utility(state1))
    else: # provide non-payment proof
        state2 = copy_state(state)
        state2["nonpayment_proof"] = True
        state2["who_proved"] = A
        branch_further_actions_A[npp] = leaf(compute_utility(state2))
    
    # burn collateral
    state3 = copy_state(state)
    state3["burning"] = True
    branch_further_actions_A[burn] = leaf(compute_utility(state3))

    return branch(A, branch_further_actions_A)

def liquidation(state : Dict) -> Tree:
    branch_liquidation = {}

    # liquidate enough
    # math: 
    # state["collateral"]*priceFLR >= crSafety * (state["number_backed_assets"]-n)* priceBTC>
    # n = crSafety * state["number_backed_assets"]* priceBTC - state["collateral"]*priceFLR / (crSafety* priceBTC)
    INITIAL_CONSTRAINTS.append(n == crSafety * state["number_backed_assets"]* priceBTC - state["collateral"]*priceFLR / (crSafety* priceBTC))

    state1 = copy_state(state)
    state1["number_backed_assets"] = state["number_backed_assets"] - n
    state1["collateral"] = state["collateral"] - n * priceBTC / priceFLR
    state1["extra_balance"][L] = state1["extra_balance"][L] + n * priceBTC * premium
    state1["extra_balance"][A] = state1["extra_balance"][A] - n * priceBTC * premium
    branch_liquidation[le] = further_actions_A(state1)

    # liquidate not enough
    # we already have n > amt in the initial constraints, so we can just use amt here

    state2 = copy_state(state)
    state2["number_backed_assets"] = state["number_backed_assets"] - amt
    state2["collateral"] = state["collateral"] - amt * priceBTC / priceFLR
    state2["extra_balance"][L] = state2["extra_balance"][L] + amt * priceBTC * premium
    state2["extra_balance"][A] = state2["extra_balance"][A] - amt * priceBTC * premium
    branch_liquidation[lne] = further_actions_A(state2)

    return branch(L, branch_liquidation)

def conditional_node(state : Dict) -> Tree:
    branch_conditional_node = {}

    # liquidation is possible
    liq = state["collateral"]*priceFLR < cr * state["number_backed_assets"]* priceBTC

    branch_conditional_node[liq] = liquidation(state)

    # liquidation is not possible
    no_liq = state["collateral"]*priceFLR >= cr * state["number_backed_assets"]* priceBTC
    branch_conditional_node[no_liq] = further_actions_A(state)

    return condition(branch_conditional_node)


# generate the game tree
def generate_tree(state: Dict) -> Tree:

    branch_actions = {} 

    # payment and payment proof 
    state1 = copy_state(state)
    state1["payment_happened"] = True
    state1["payment_proof"] = True
    state1["who_proved"] = M
    branch_actions[pp] = leaf(compute_utility(state1))

    # payment and no payment proof
    state2 = copy_state(state)
    state2["payment_happened"] = True
    branch_actions[npp] = conditional_node(state2)

    # Ignore
    state3 = copy_state(state)
    branch_actions[I] = conditional_node(state3)
    
    return branch(M, branch_actions)


#################################################################################################################
####################################### end of tree generation functions ########################################
#################################################################################################################


# generate the game tree assuming the player listed first in PLAYERS has the first turn
TREE = generate_tree(initial_state)

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