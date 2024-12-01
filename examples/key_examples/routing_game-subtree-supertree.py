from dsl import *
import itertools
import re
import subprocess
import json
import sys

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

How to adapt the generation based on the number of players:
- Make sure you list all players in `ps`, e.g.
    - for 3-player routing: ps = PLAYERS = players('A', 'I', 'B')
    - for 4-player routing: ps = PLAYERS = players('A', 'I1', 'I2', 'B')
- Make sure, you provide the honest utility of each player, e.g
    - for 4-player routing:
        HONEST_UTILITIES = [
        {
            "utility": [
                {
                "player": "A",
                "value": "rho"
                },
                {
                "player": "I1",
                "value": "f"
                },
                {
                "player": "I2",
                "value": "f"
                },
                {
                "player": "B",
                "value": "rho"
                }
            ]
        }

Call this script from the checkmate build folder.
    -  python3 ../examples/key_examples/routing_game-subtree-supertree.py
        
]
"""

PRINT_HISTORIES = False

ps = PLAYERS = players('A', 'I', 'B')
S_H, U, J, I_L, I_U= ACTIONS = actions(
    'S_H', 'U', 'J', 'I_L', 'I_U')
epsilon, rho = INFINITESIMALS = infinitesimals('epsilon', 'rho')
m, f = CONSTANTS = constants('m', 'f')

INITIAL_CONSTRAINTS = [
    rho > 0,
    epsilon > 0,
    f > 0,
    m > 0
]

#dishonest amounts different from honest amounts (first deviation only)
for i in range(len(ps)-1):
    CONSTANTS.append(NameExpr(f"a_{ps[i]}_{ps[i]}"))
    INITIAL_CONSTRAINTS.append(NameExpr(f"a_{ps[i]}_{ps[i]}") !=  m + (len(ps) - 2 - i) * f)
    for j in range(i,len(ps)-1):
        if j != i:
            CONSTANTS.append(NameExpr(f"a_{ps[i]}_{ps[j]}"))
        INITIAL_CONSTRAINTS.append(NameExpr(f"a_{ps[i]}_{ps[j]}") >= 0 )

WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

recursion_depth = 0

actions_for_sharing_secrets = set()
actions_for_locking = set()
constants_for_wrong_amounts = set()


def secret_sharing_sets(secrets_to_share: Dict[Player, List[Player]]):
    powersets = []
    for key in secrets_to_share:
        powerset = [subset
                    for length in range(len(secrets_to_share[key]) + 1)
                    for subset in itertools.combinations(secrets_to_share[key], length)]
        powersets.append(powerset)
    for ll in itertools.product(*powersets):
        yield ll


def prev_player(player):
    i = ps.index(player)
    return ps[i-1]


def player_plus_one(player):
    i = ps.index(player)
    ii = (i + 1) % len(ps)
    return ps[ii]


def next_players(player, state):
    i = state["time_orderings"].index(player)
    return state["time_orderings"][:i]


def final(state):
    for p in ps:
        if state[p]["contract"] == "locked":
            return False
    for p in ps:
        if state[p]["contract"] == "kaput":
            state[p]["contract"] = "expired"
    return True


def utility_leaf(state, B_sharing):
    ut = {player: 0 for player in ps}
    for player in ps:
        if player == ps[-1]:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + rho - m + state[player]["amount_to_unlock"]
                ut[prev_player(player)] = ut[prev_player(player)] - state[player]["amount_to_unlock"]
                ut[ps[0]] = ut[ps[0]] + rho + m + (len(ps) - 2) * f
            elif state[player]["contract"] == "expired":
                ut[prev_player(player)] = ut[prev_player(player)] - epsilon
                # if the last player was sharing secrets, then he has to ship the goods
                if B_sharing:
                    ut[player] = ut[player] + rho - m
                    ut[ps[0]] = ut[ps[0]] + rho + m + (len(ps) - 2) * f
        else:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + state[player]["amount_to_unlock"]
                ut[prev_player(player)] = ut[prev_player(player)] - state[player]["amount_to_unlock"]
            elif state[player]["contract"] == "expired":
                ut[prev_player(player)] = ut[prev_player(player)] - epsilon
    return ut


def copy_state(state):
    state1 = {}
    state1["time_orderings"] = state["time_orderings"][:]
    state1["eq_secrets"] = [[p for p in s] for s in state["eq_secrets"]]
    for player in ps:
        state1[player] = {}
        state1[player]["contract"] = state[player]["contract"]
        state1[player]["amount_to_unlock"] = state[player]["amount_to_unlock"]
        state1[player]["secrets"] = {p: state[player]["secrets"][p] for p in ps}
        state1[player]["ignoreshare"] = {p: state[player]["ignoreshare"][p] for p in ps}
    return state1


def players_who_can_unlock(state):
    knowers = set()
    for p in ps:
        if state[p]["secrets"][prev_player(p)]:
            if state[p]["contract"] == "locked":
                knowers.add(p)
    return knowers


def next_player(state):
# prio1: the next player is the one with the next time-out, who knows the secret and current state of contract is locked
# prio2: the next player is the one with the earliest time-out who can share
# prio3: if the is no possible next player, every locked contract expires and we reach a leaf of the game tree
    next_p = None
    state2 = copy_state(state)
    candidates = players_who_can_unlock(state)
    if candidates:
        for p in state["time_orderings"]:
            if p in candidates:
                next_p = p
                break
        return next_p, state2
    for p in state["time_orderings"]:
        secrets_p_knows = {pl for pl in ps if state[p]["secrets"][pl]}
        secrets_to_share = secrets_p_knows - {pl for pl in ps if state[p]["ignoreshare"][pl]}
        secrets_to_share = remove_pointless_sharing(state, list(secrets_to_share))
        sharing_dict = {s: [] for s in secrets_to_share}
        for secret in secrets_to_share:
            for player in set(ps) - {p}:
                if not state[player]["secrets"][secret]:
                    sharing_dict[secret].append(player)
                    next_p = p
        if next_p is not None:
            break
    if next_p is None:
        for p in ps:
            if state2[p]["contract"] == "locked":
                state2[p]["contract"] = "expired"
    return next_p, state2


def share_secret_action(sharing_instance):
    # Actions for sharing secrets: S_S_[[],[],[A, B], [], [E1]]
    return Action(f"S_S{sharing_instance}")


def align_secret_knowledge(state):
    def update_dict(d, eq_classes):
        for eq_class in eq_classes:
            tmp = [d[p] for p in d if p in eq_class]
            if any(tmp):
                for p in eq_class:
                    d[p] = True
    for player in ps:
        update_dict(state[player]["secrets"], state["eq_secrets"])
        update_dict(state[player]["ignoreshare"], state["eq_secrets"])


def recognise_kaput(state):
    # recognise which contracts are kaput
    for i in range(len(ps)-1):
        player = ps[i]
        flag = False
        for p in ps:
            if state[p]["secrets"][player]:
                flag = True
                break
        if not flag:
            state[ps[i+1]]["contract"] = "kaput"


def remove_pointless_sharing(state, secrets_to_share_representatives):
    # secrets of contracts that are unlocked or expired are pointless to share
    useful = []
    for eq_class in state["eq_secrets"]:
        if eq_class[0] in secrets_to_share_representatives:
            for secret in eq_class:
                i = ps.index(secret)
                if not i == len(ps)-1 and state[ps[i+1]]["contract"] == "locked":
                    useful.append(eq_class[0])
                    break
    return useful


def generate_routing_unlocking(player: Player, state, B_sharing, history):
    if PRINT_HISTORIES:
        print(history)
    # print(player)
    # print(state)
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    global recursion_depth
    depth = len(history.split(";"))
    if depth > recursion_depth:
        recursion_depth = depth
    if final(state):
        return leaf(utility_leaf(state, B_sharing))
    else:
        # if all(state[player]["ignoreshare"].values()):
        #     raise Exception(f"It should not be player {player}'s turn, because they have ignored sharing secrets.")
        branch_actions = {}
        # Sharing is caring
        secrets_player_knows = {pl for pl in ps if state[player]["secrets"][pl]}
        secrets_to_share = secrets_player_knows - {pl for pl in ps if state[player]["ignoreshare"][pl]}
        secrets_to_share_representatives = []
        for eq_class in state["eq_secrets"]:
            if eq_class[0] in secrets_to_share:
                secrets_to_share_representatives.append(eq_class[0])
        secrets_to_share_representatives = remove_pointless_sharing(state, secrets_to_share_representatives)
        if history:
            pprev_player, prev_action = history[:-1].split(";")[-1].split(".")
        else:
            pprev_player = None
            prev_action = None
        if pprev_player != str(player) or "S_S" not in prev_action:
            sharing_dict = {s: [] for s in ps}
            for secret in secrets_to_share_representatives:
                for p in set(ps) - {player}:
                    if not state[p]["secrets"][secret]:
                        sharing_dict[secret].append(p)
            for sharing_instance in secret_sharing_sets(sharing_dict):
                B_sharing1 = B_sharing
                if player == ps[-1] and list(sharing_instance) != [tuple() for _ in ps]:
                    B_sharing1 = True
                state1 = copy_state(state)
                for i in range(len(ps)):
                    for person in sharing_instance[i]:
                        state1[person]["secrets"][ps[i]] = True
                    if state1[player]["secrets"][ps[i]]:
                        state1[player]["ignoreshare"][ps[i]] = True
                align_secret_knowledge(state1)
                next_p, state2 = next_player(state1)
                actions_for_sharing_secrets.add(f"S_S{sharing_instance}")
                branch_actions[share_secret_action(sharing_instance)] = generate_routing_unlocking(next_p, state2, B_sharing1, history + str(player) + "." + str(share_secret_action(sharing_instance)) + ";")
        if state[player]["contract"] == "locked" and state[player]["secrets"][prev_player(player)]:
            # Action unlock
            state1 = copy_state(state)
            state1[player]["contract"] = "unlocked"
            state1[prev_player(player)]["secrets"][prev_player(player)] = True
            align_secret_knowledge(state1)
            next_p, state2 = next_player(state1)
            branch_actions[U] = generate_routing_unlocking(next_p, state2, B_sharing, history + str(player) + ".U;")
            # Ignoring unlock
            state3 = copy_state(state)
            state3[player]["contract"] = "expired"
            for p in next_players(player, state):
                if state[p]["contract"] == "locked":
                    state3[p]["contract"] = "expired"
            # the next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p, state4 = next_player(state3)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state4, B_sharing, history + str(player) + ".I_U;")

        #imlpied by empty sharing_instance
        # else:
        #     # Ignoring sharing
        #     state1 = copy_state(state)
        #     for secret in secrets_to_share:
        #         state1[player]["ignoreshare"][secret] = True
        #     next_p, state2 = next_player(state1)
        #     branch_actions[I_S] = generate_routing_unlocking(next_p, state2, history + str(player) + ".I_S;")
        if not branch_actions:
            raise Exception("Empty branch, next player chosen wrong")
        return branch(player, branch_actions)

# state[p] = [<state of the contract>,<knowledge of secrets>,<igoresharing secrets>,<equivalence classes of secrets>]
# secrets are represented by players who wrote the HTCL contract with this hash
# ignoresharing with key p, means not sharing the secret that p used to lock their contract with anyone


def locking_action(deviator, slot, eq_class):
    return f"L_({deviator},{slot},{eq_class})"


def generate_routing_locking(player, state, deviator, history, actions_so_far):
    if PRINT_HISTORIES:
        print(history)
    branch_actions = {}

    def aux_locking(player, new_state, deviator, history):
        # time orderings
        positions = [i for i in range(len(ps)) if state["time_orderings"][i] is None]
        for i in positions:
            new_state1 = copy_state(new_state)
            new_state1["time_orderings"][i] = player
            # eq classes of secrets
            for j in range(len(state["eq_secrets"])):
                new_state2 = copy_state(new_state1)
                new_state2["eq_secrets"][j].append(player)
                new_state2[player_plus_one(player)]["contract"] = "locked"
                action = locking_action(deviator, i, new_state2["eq_secrets"][j])
                actions_for_locking.add(action)
                if player == ps[-2]:
                    align_secret_knowledge(new_state2)
                    if new_state2["time_orderings"].count(None) != 1:
                        raise Exception("Locking phase went wrong, there are several or zero positions unspecified in time orderings")
                    else:
                        position = new_state2["time_orderings"].index(None)
                        new_state2["time_orderings"][position] = ps[-1]
                    #branch_actions[Action(action)] = dict()
                    tree = generate_routing_unlocking(ps[-1], new_state2, False, history + str(player) + f".{action};")
                    honest_histories = []
                    honest_utilities = []
                    #new_history = history + str(player) + f".{action}"
                    result_file = 'subtree_result_history0.txt'

                    along_honest = True
                    updated_actions = actions_so_far + [Action(action)]

                    if len(HONEST_HISTORIES[0]) < len(updated_actions):
                        along_honest = False
                    else:
                        for i in range(len(updated_actions)):
                            if str(HONEST_HISTORIES[0][i]) != str(updated_actions[i]):
                                along_honest = False
                                break

                    if along_honest:
                        honest_histories = [HONEST_HISTORIES[0][len(updated_actions):]] 
                    else:
                        result_file = 'subtree_result_utility0.txt'
                        honest_utilities = HONEST_UTILITIES 

                    #filename = 'routing_game-subtree-' + new_history + '.json'         
                    filename = 'subtree.json'

                    with open(filename, 'w') as f1:
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
                            honest_histories,
                            honest_utilities,
                            tree,
                            f1
                        )
                    

                    ## call checkmate with this file in subtree mode 
                    subprocess.run(['./checkmate', filename, '--subtree'])

                    ## read produced file and put result of subtree back in supertree
                    with open(result_file, 'r') as result:
                        result_content = result.read()
                        try:
                            json_result = json.loads(result_content)
                            branch_actions[Action(action)] = json_result
                        except json.JSONDecodeError as e:
                            print(f"Error decoding JSON from file {result_file}: {e}")

                    

                else:
                    branch_actions[Action(action)] = generate_routing_locking(player_plus_one(player), new_state2, deviator, history + str(player) + f".{action};", actions_so_far + [Action(action)])
            # I am my own eq class therefore I know my own secret
            new_state1["eq_secrets"].append([player])
            new_state1[player]["secrets"][player] = True
            new_state1[player_plus_one(player)]["contract"] = "locked"
            action = locking_action(deviator, i, new_state1["eq_secrets"][-1])
            actions_for_locking.add(action)
            if player == ps[-2]:
                align_secret_knowledge(new_state1)
                # print(history + str(player) + f".{action};")
                if new_state1["time_orderings"].count(None) != 1:
                    raise Exception("Locking phase went wrong, there are several or zero positions unspecified in time orderings")
                else:
                    position = new_state1["time_orderings"].index(None)
                    new_state1["time_orderings"][position] = ps[-1]
                #branch_actions[Action(action)] = dict()
                tree = generate_routing_unlocking(ps[-1], new_state2, False, history + str(player) + f".{action};")
                honest_histories = []
                honest_utilities = []
                #new_history = history + str(player) + f".{action}"
                result_file = 'subtree_result_history0.txt'
                
                along_honest = True
                updated_actions = actions_so_far + [Action(action)]

                if len(HONEST_HISTORIES[0]) < len(updated_actions):
                    along_honest = False
                else:
                    for i in range(len(updated_actions)):
                        if str(HONEST_HISTORIES[0][i]) != str(updated_actions[i]):
                            along_honest = False
                            break

                if along_honest:
                    honest_histories = [HONEST_HISTORIES[0][len(updated_actions):]] 
                else:
                    result_file = 'subtree_result_utility0.txt'
                    honest_utilities = HONEST_UTILITIES   

                #filename = 'routing_game-subtree-' + new_history + '.json'         
                filename = 'subtree.json'          

                with open(filename, 'w') as f2:
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
                        honest_histories,
                        honest_utilities,
                        tree,
                        f2
                    )

                ## call checkmate with this file in subtree mode 
                subprocess.run(['./checkmate', filename, '--subtree'])

                ## read produced file and put result of subtree back in supertree
                with open(result_file, 'r') as result:
                    result_content = result.read()
                    try:
                        json_result = json.loads(result_content)
                        branch_actions[Action(action)] = json_result
                    except json.JSONDecodeError as e:
                        print(f"Error decoding JSON from file {result_file}: {e}")
                    
            else:
                branch_actions[Action(action)] = generate_routing_locking(player_plus_one(player), new_state1, deviator, history + str(player) + f".{action};", actions_so_far + [Action(action)])

    if deviator is None:
        # case honest amount
        state1 = copy_state(state)
        i = ps.index(player)
        state1[ps[i+1]]["amount_to_unlock"] = m + (len(ps) - 2 - i) * f
        aux_locking(player, state1, deviator, history)
        deviator = player
    # case dishonest amount
    state2 = copy_state(state)
    i = ps.index(player)
    state2[ps[i+1]]["amount_to_unlock"] = NameExpr(f"a_{deviator}_{player}")
    constants_for_wrong_amounts.add(f"a_{deviator}_{player}")
    aux_locking(player, state2, deviator, history)
    # case ignore locking
    ut = {}
    for j in range(len(ps)):
        if j < i:
            ut[ps[j]] = - epsilon
        else:
            ut[ps[j]] = 0
    branch_actions[I_L] = leaf(ut)
    if PRINT_HISTORIES:
        print(history + str(player) + f".I_L;")
    return branch(player, branch_actions)


initial_state = {
    "eq_secrets": [[ps[-1]]],
    "time_orderings": [None for _ in ps]
}
for player in ps:
    initial_state[player] = {}
    initial_state[player]["contract"] = "null"
    initial_state[player]["amount_to_unlock"] = None
    initial_state[player]["secrets"] = {p: False for p in ps}
    initial_state[player]["ignoreshare"] = {p: False for p in ps}
initial_state[ps[-1]]["secrets"][ps[-1]] = True

honest = ["S_H"]
eq_cl = [ps[-1]]
for i in range(len(ps)-1):
    eq_cl.append(ps[i])
    honest.append(f"L_(None,{len(ps)-1-i},{eq_cl})")
for i in range(len(ps)-1):
    honest.append("U")

HONEST_HISTORIES = [[Action(a) for a in honest]]

HONEST_UTILITIES = [
    {
      "utility": [
        {
          "player": "A",
          "value": "rho"
        },
        {
          "player": "I",
          "value": "f"
        },
        {
          "player": "B",
          "value": "rho"
        }
      ]
    }
]

for act in actions_for_sharing_secrets:
    ACTIONS.append(Action(act))

for act in actions_for_locking:
    ACTIONS.append(Action(act))

locking_tree = generate_routing_locking(ps[0], initial_state, None, "", [Action('S_H')])

#for const in constants_for_wrong_amounts:
    #CONSTANTS.append(NameExpr(const))

routing_tree = branch(ps[-1], {
    J: leaf({p: 0 for p in ps}),
    S_H: locking_tree
})

### This part here is for debugging
intermediate_state = {
    "eq_secrets": [[p for p in ps]],
    "time_orderings": [ps[2], ps[1], ps[0]]
}
for player in ps:
    intermediate_state[player] = {}
    intermediate_state[player]["contract"] = "null"
    intermediate_state[player]["amount_to_unlock"] = None
    intermediate_state[player]["secrets"] = {p: False for p in ps}
    intermediate_state[player]["ignoreshare"] = {p: False for p in ps}
intermediate_state[ps[2]]["secrets"][ps[-1]] = True
intermediate_state[ps[2]]["amount_to_unlock"] = m
intermediate_state[ps[2]]["contract"] = "locked"
intermediate_state[ps[1]]["amount_to_unlock"] = m + f
intermediate_state[ps[1]]["contract"] = "locked"
align_secret_knowledge(intermediate_state)

# unlocking_tree = generate_routing_unlocking(ps[-1], intermediate_state, "")
### Debugging part finished

TREE = routing_tree

with open('routing_game-supertree.json', 'w') as f3:
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
        TREE,
        f3
    )
