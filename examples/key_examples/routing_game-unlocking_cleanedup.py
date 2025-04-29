from dsl import *
import itertools
import re

"""
This file generates a game model for Lightning's routing protocol. To set the number of intermediaries to n,
include n many labels in players() between A and B.

Design choices for routing:
An HTLC has the following parameters:
- y: hash value of the secret that has to be used to unlock the HTLC.
- v: the amount of funds locked in the HTLC.
- t: time out, after which the funds are reassigned to the HTLC's initiator.

All of these parameters could be misused in a possible attack. Therefore, the actions the players can take in the game need to
reflect the choices of parameters. To correctly model the possible actions and utilities in each step, we track the parameters
in a state with the following structure:

state = {
    "eq_secrets": <equivalence classes of secrets (list of lists)>,
    "time_orderings": <list of players according to the HLTCs' time outs>,
    <player>: {"contract": <'locked','unlocked','expired','null'>,
        "amount_to_unlock": <linear expression, None>,
        "secrets": {<player2>: <True, False depending on whether player knows the secret whose hash player2 used in their HTLC>},
        "ignoreshare": {<player3>:<True, False, depending on whether player decided not to share player3's secret with anyone anymore>}},
}

Secrets: In the honest case there is only one secret (player B's) whose hash everyone uses to lock their contracts. However,
players could use different secrets and their hashes in the contracts. Some of these secrets can be the same.
This is recorded in the state with "eq_secrets". For example if eq_secrets" is [[A, I], [B, E1, E2]], then A and I used the same secret's hash,
but different from the one B, E1 and E2 used.

Knowledge of secrets: Since there might be multiple secrets, we have to keep track of whose secret each player knows. This is modeled in the
dictionary "secrets" for each player. Note that since some secrets can be identical, we need to align the knowledge of secrets according to the equivalence
classes.

Sharing of secrets: In the honest case no player would share a secret. However, secret sharing can lead to possible attacks, so we model
this behavior. A player who knows a secret can choose to share it with other players or ignore this option, which we record in the "ignoreshare" dictionary.

Time orderings: It only matters in which order the contracts expire. Thus, we model time outs by the ordering the players according
to their contracts' time outs. The first element in the list has the earliest time out.

Amount to unlock and contract: Each contract that was set up can be in three different states: "locked", i.e. player can unlock it before the time out
if they know the corresponding secret, "unlocked", or "expired" if the contract has already timed out.
Note that the contract is attributed to the player who can unlock. This also holds for the amount to unlock.


Other design choices:

1) The players can choose between the following actions:
    - In the initiation phase, i.e. before contracts are locked:
        *)S_H: B can choose to share the hash to their secret with A and thereby initiate the locking phase.
        *)J: B can choose to ignore the possible trade.
    - In the locking phase:
        *) L_(<amount_deviator>,<time_ordering_placement>,<equivalence_class>): e.g. L_(A,2,[B, I]) is an action that player I can choose.
           It means that A was the first to deviate in the locked amount, I's contract expires second and I used the same hash as B.
           Note that in the honest case, the amount deviator is set to None, as nobody deviates.
        *) I_L: Ignore to lock a contract.
    - In the unlocking phase:
        *) U: Unlocking the contract.
        *) I_U: Ignore to unlock the contract. This implies expiration of the contract.
        *) S_S((<players to share A's secret with>),...,(<players to share B's secret with>)):
           Sharing the secrets. Note that S_S((),...,()) means sharing with nobody.

2) Choosing the next player is an important design choice in game models.
    - In the locking phase (set up of contracts), the next player is chosen according to the planned route.
    - We start the unlocking phase with player B. After that the next player is chosen according to the following priorities:
        *) Priority 1: The next player is the one whose contract expires next and who knows the secret.
        *) Priority 2: The next player is the one with the earliest time-out, who can share a secret.
        *) Priority 3: If there is no possible next player, every locked contract expires and we reach a leaf of the game tree.

3) Wlog to prune the tree we limit the sharing of secrets in the following ways:
    - Sharing secrets can only happen in the unlocking phase, that is when all contracts are already set up.
      If sharing secrets only happens in the unlocking phase, we will still capture possible attacks (including collusion),
      with even worse utility (-epsilon instead of 0).
    - At the same time a person can share multiple secrets with multiple players (who do not know them already).
      As a consequence, sharing secrets in two consecutive actions by the same player is not permitted.
    - Sharing a secret with a subset of players implies ignoring the sharing of this secret with all other players.
    - Sharing secrets, which were only used in contracts which are already unlocked or expired, is pointless and therefore not modeled.

4) We assume a fair trade behind a payment, that means A pays B in exchange for some goods. In the honest case both A and B benefit from
such a trade. This is modeled by the infinitesimal value rho, which both A and B get assigned once B sent the goods.
In our model, if B unlocks the contract, they are obligated to send the goods (proof of payment). But also if B is sharing the secret
there is proof that B engaged in the unlocking and is thus "legally" obligated to send the goods.

5) If a player locks with a wrong amount, we model this amount with a variable and include a constraint that it is different
from the correct amount. The variable is named "a_<first-deviator>_<current-player>". Once one player locks with a wrong amount, the amounts in the following contracts are also modeled
with a variable (possibly equal to the correct amount). This way we capture all possible cases, but prune the game tree at the same time.

6) Wlog we assume that everytime a player locks a contract with a new hash, they also know the corresponding secret. Otherwise,
no one could ever unlock the contract and therefore it is security-equivalent to not creating a contract at all.
"""


PLAYERS = players('A', 'I1', 'I2', 'I3', 'B')

U, I_U = ACTIONS = actions('U', 'I_U')
epsilon, rho = INFINITESIMALS = infinitesimals('epsilon', 'rho')
m, f = CONSTANTS = constants('m', 'f')

INITIAL_CONSTRAINTS = [
    rho > 0,
    epsilon > 0,
    f > 0,
    m > 0
]

WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []




def is_final(state):
    for p in PLAYERS:
        if state[p]["contract"] == "locked":
            return False
    return True


def compute_utility(state):
    ut = {player: 0 for player in PLAYERS}
    for player in PLAYERS:
        prev_player = PLAYERS[PLAYERS.index(player)-1]
        if player == PLAYERS[-1]:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + rho - m + state[player]["amount_to_unlock"]
                ut[prev_player] = ut[prev_player] - state[player]["amount_to_unlock"]
                ut[PLAYERS[0]] = ut[PLAYERS[0]] + rho + m + (len(PLAYERS) - 2) * f
            elif state[player]["contract"] == "expired":
                ut[prev_player] = ut[prev_player] - epsilon
                # if the last player was sharing secrets, then he has to ship the goods
                if state['B_shared']:
                    ut[player] = ut[player] + rho - m
                    ut[PLAYERS[0]] = ut[PLAYERS[0]] + rho + m + (len(PLAYERS) - 2) * f
        else:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + state[player]["amount_to_unlock"]
                ut[prev_player] = ut[prev_player] - state[player]["amount_to_unlock"]
            elif state[player]["contract"] == "expired":
                ut[prev_player] = ut[prev_player] - epsilon
    return ut


def copy_state(state):
    state1 = {}
    state1["B_shared"] = state["B_shared"]
    for player in PLAYERS:
        state1[player] = {}
        state1[player]["contract"] = state[player]["contract"]
        state1[player]["amount_to_unlock"] = state[player]["amount_to_unlock"]
        state1[player]["secret"] = state[player]["secret"]
        state1[player]["ignoreshare"] = {p: state[player]["ignoreshare"][p] for p in PLAYERS}
    return state1


def next_player(state):
    # prio1: the next player is the one with the next time-out, who knows the secret and current state of contract is locked
    for p in PLAYERS[::-1]:
        if state[p]["secret"] and state[p]["contract"] == "locked":
            return p, state

    # prio2: the next player is the one with the earliest time-out who can share
    for p in PLAYERS[::-1]:
        if state[p]["secret"]:
            for share_with in PLAYERS:
                if not state[p]["ignoreshare"][share_with] and not state[share_with]["secret"]:
                    return p, state

    # prio3: if there is no possible next player, every locked contract expires and we reach a leaf of the game tree
    state1 = copy_state(state)
    for p in PLAYERS:
        if state1[p]["contract"] == "locked":
            state1[p]["contract"] = "expired"
    return None, state1

def powerset(share_secret_with: List) -> List:
    if len(share_secret_with)>0:
        powerset = [subset
            for length in range(len(share_secret_with) + 1)
            for subset in itertools.combinations(share_secret_with, length)]
    else:
        powerset = []
    return powerset

def generate_routing_unlocking(player: Player, state, history):
    if is_final(state):
        return leaf(compute_utility(state))
    else:
        branch_actions = {}
        assert state[player]["secret"]
        # Secret Sharing 
        # computing who the current player can still share the secret with
        share_secret_with = []
        for share_with in PLAYERS:
            if not state[player]["ignoreshare"][share_with] and not state[share_with]["secret"]:
                share_secret_with.append(share_with)

        # if sharing is still possible (i,e, if share_secret_with is not empty), iterate over all subsets of players to share the secret with
        for subset in powerset(share_secret_with):
            state1 = copy_state(state)
            if player == PLAYERS[-1] and subset != tuple():
                state1['B_shared'] = True
            # when I could have shared the secret with so, but chose not to, I automatically ignore the sharing = "ignoreshare"
            for p in share_secret_with:
                if p in subset:
                    state1[p]["secret"] = True
                else:
                    state1[player]["ignoreshare"][p] = True

            next_p, state2 = next_player(state1)
            ACTIONS.append(Action(f"S_S{subset}"))
            branch_actions[Action(f"S_S{subset}")] = generate_routing_unlocking(next_p, state2, history + str(player) + "." + f"S_S{subset}" + ";")

        if state[player]["contract"] == "locked" and state[player]["secret"]:
            # Action unlock
            state1 = copy_state(state)
            state1[player]["contract"] = "unlocked"
            state1[PLAYERS[PLAYERS.index(player)-1]]["secret"] = True
            next_p, state2 = next_player(state1)
            branch_actions[U] = generate_routing_unlocking(next_p, state2, history + str(player) + ".U;")
            # Ignoring unlock
            state3 = copy_state(state)
            # player's contract expires and hence also all players' to the right
            for p in PLAYERS[PLAYERS.index(player):]:
                if state[p]["contract"] == "locked":
                    state3[p]["contract"] = "expired"
            next_p, state4 = next_player(state3)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state4, history + str(player) + ".I_U;")

        if not branch_actions:
            raise Exception("Empty branch, next player chosen wrong")
        
        return branch(player, branch_actions)




initial_state = {"B_shared": False}
for player in PLAYERS:
    initial_state[player] = {}
    initial_state[player]["contract"] = "locked"
    initial_state[player]["amount_to_unlock"] = m + (len(PLAYERS)-PLAYERS.index(player)-1)*f
    initial_state[player]["secret"] = False
    initial_state[player]["ignoreshare"] = {p: False for p in PLAYERS}
initial_state[PLAYERS[-1]]["secret"] = True
initial_state[PLAYERS[0]]["contract"] = "null"
initial_state[PLAYERS[0]]["amount_to_unlock"] = None

TREE = generate_routing_unlocking(PLAYERS[-1], initial_state, "")

HONEST_HISTORIES = [[U,U,U,U]]

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
