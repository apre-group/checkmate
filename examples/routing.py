from os import stat
from dsl import *
from typing import Union
import copy
import itertools

A, E1, I, E2, B = players('A', 'E1', 'I', 'E2', 'B')
S_H, L, U, J, S_S, L_T, L_H, L_A, S_SE1, S_SI, I_L, I_U, I_S, S_SA, S_SE2, S_SB = actions(
    'S_H', 'L', 'U', 'J', 'S_S', 'L_T', 'L_H', 'L_A', 'S_SE1', 'S_SI', 'I_L', 'I_U', 'I_S', 'S_SA', 'S_SE2', 'S_SB'
)
epsilon, rho, todoo = infinitesimals('epsilon', 'rho', 'todo')
m, f = constants('m', 'f')

initial_constraints(
    rho > 0,
    epsilon > 0,
    f > 0,
    m > 0
)

weak_immunity_constraints()
collusion_resilience_constraints()
practicality_constraints()

honest_histories((U, U, U, U))


def leaf5(a: LExpr, b: LExpr, c: LExpr, d: LExpr, e: LExpr) -> Leaf:
    return leaf({A: a, E1: b, I: c, E2: d, B: e})


todo = leaf5(todoo, todoo, todoo, todoo, todoo)

recursion_depth = 0

ps = [A, E1, I, E2, B]


#Actions for sharing secrets: S_S_[[],[],[A, B], [], [E1]]
actions_for_sharing_secrets = set()
# powerset = [subset
#             for length in range(len(ps)+1)
#             for subset in itertools.combinations(ps, length)]
# for ll in itertools.product(powerset, repeat=5):
#     ACTIONS.append(Action(f"S_S_{ll}"))


def secret_sharing_sets(secrets_to_share: Dict[Player, List[Player]]):
    powersets = []
    for key in secrets_to_share:
        powerset = [subset
                    for length in range(len(secrets_to_share[key]) + 1)
                    for subset in itertools.combinations(secrets_to_share[key], length)]
        powersets.append(powerset)
    for ll in itertools.product(*powersets):
        yield ll


# for x in secret_sharing_sets({A: [], E1: [A], I: [], E2: [], B: [E1, E2]}):
#     print(x)


def prev_player(player):
    players = [A, E1, I, E2, B]
    i = players.index(player)
    return players[i-1]


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


class Utility_leaf:

    def __init__(self, t: Tuple[LExpr]) -> None:
        self.utility = t

    def __add__(self, other):
        pointwise_add = [self.utility[i] + other.utility[i] for i in range(len(self.utility))]
        return Utility_leaf(tuple(pointwise_add))


def utility_leaf(state):
    ut = Utility_leaf((0,0,0,0,0))
    if state[B]["contract"] == "unlocked":
        ut = ut + Utility_leaf((rho+m+3*f,0,0,-m,rho))
    elif state[B]["contract"] == "expired":
        ut = ut + Utility_leaf((0,0,0,-epsilon,0))
    if state[E2]["contract"] == "unlocked":
        ut = ut + Utility_leaf((0,0,-m-f,m+f,0))
    elif state[E2]["contract"] == "expired":
        ut = ut + Utility_leaf((0,0,-epsilon,0,0))
    if state[I]["contract"] == "unlocked":
        ut = ut + Utility_leaf((0,-m-2*f,m+2*f,0,0))
    elif state[I]["contract"] == "expired":
        ut = ut + Utility_leaf((0,-epsilon,0,0,0))
    if state[E1]["contract"] == "unlocked":
        ut = ut + Utility_leaf((-m-3*f,m+3*f,0,0,0))
    elif state[E1]["contract"] == "expired":
        ut = ut + Utility_leaf((-epsilon,0,0,0,0))
    return ut


def copy_state(state):
    state1 = {}
    state1["time_orderings"] = state["time_orderings"][:]
    state1["eq_secrets"] = [[p for p in s] for s in state["eq_secrets"]]
    for player in ps:
        state1[player] = {}
        state1[player]["contract"] = state[player]["contract"]
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


def generate_routing_unlocking(player: Player, state, history):
    # print(history)
    # print(player)
    # print(state)
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    global recursion_depth
    depth = len(history.split(";"))
    if depth > recursion_depth:
        recursion_depth = depth
    if final(state):
        return leaf5(*utility_leaf(state).utility)
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
                state1 = copy_state(state)
                for i in range(len(ps)):
                    for person in sharing_instance[i]:
                            state1[person]["secrets"][ps[i]] = True
                    if state1[player]["secrets"][ps[i]]:
                            state1[player]["ignoreshare"][ps[i]] = True
                align_secret_knowledge(state1)
                next_p, state2 = next_player(state1)
                actions_for_sharing_secrets.add(f"S_S{sharing_instance}")
                branch_actions[share_secret_action(sharing_instance)] = generate_routing_unlocking(next_p, state2, history + str(player) + "." + str(share_secret_action(sharing_instance)) + ";")
        if state[player]["contract"] == "locked" and state[player]["secrets"][prev_player(player)]:
            # Action unlock
            state1 = copy_state(state)
            state1[player]["contract"] = "unlocked"
            state1[prev_player(player)]["secrets"][prev_player(player)] = True
            align_secret_knowledge(state1)
            next_p, state2 = next_player(state1)
            branch_actions[U] = generate_routing_unlocking(next_p, state2, history + str(player) + ".U;")
            # Ignoring unlock
            state3 = copy_state(state)
            state3[player]["contract"] = "expired"
            for p in next_players(player, state):
                if state[p]["contract"] == "locked":
                    state3[p]["contract"] = "expired"
            # the next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p, state4 = next_player(state3)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state4, history + str(player) + ".I_U;")

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


initial_state = {
    "eq_secrets": [[A, I], [B, E1, E2]],
    "time_orderings": [B, E2, I, E1, A],
    A: {"contract": "null",
        "secrets": {A: True, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E1: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    I: {"contract": "locked",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E2: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    B: {"contract": "locked",
        "secrets": {A: False, E1: True, I: False, E2: True, B: True},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}}
}

intermediate_state = {
    "eq_secrets": [[A, B, E1, I, E2]],
    "time_orderings": [B, E2, I, E1, A],
    A: {"contract": "null",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E1: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    I: {"contract": "locked",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E2: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    B: {"contract": "locked",
        "secrets": {A: True, E1: False, I: False, E2: False, B: True},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}}
}

intermediate_state1 = {
    "eq_secrets": [[A, B, E1, I, E2]],
    "time_orderings": [E2, I, B, E1, A],
    A: {"contract": "null",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E1: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    I: {"contract": "locked",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E2: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    B: {"contract": "locked",
        "secrets": {A: True, E1: False, I: False, E2: False, B: True},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}}
}

align_secret_knowledge(initial_state)
recognise_kaput(initial_state)
align_secret_knowledge(intermediate_state)
recognise_kaput(intermediate_state)
align_secret_knowledge(intermediate_state1)
recognise_kaput(intermediate_state1)

unlocking_tree = generate_routing_unlocking(B, intermediate_state1, "")
# my_tree = generate_routing_unlocking(E2, intermediate_state)

tree(unlocking_tree)

for act in actions_for_sharing_secrets:
    ACTIONS.append(Action(act))
finish()

