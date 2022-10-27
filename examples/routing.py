from os import stat
from dsl import *
from typing import Union
import copy

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


def prev_player(player):
    players = [A, E1, I, E2, B]
    i = players.index(player)
    return players[i-1]


def next_players(player):
    players = [A, E1, I, E2, B]
    i = players.index(player)
    return players[i + 1:]


def next_player(player):
    players = [A, E1, I, E2, B]
    i = players.index(player)
    return players[i+1]


def players_right_to_left():
    return [A, E1, I, E2, B][::-1]


def final(state):
    for p in ps:
        if state[p]["contract"] == "locked":
            return False
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
    state1["eq_secrets"] = {{p for p in s} for s in state["eq_secrets"]}
    for player in ps:
        state1[player] = {}
        state1[player]["contract"] = state[player]["contract"]
        state1[player]["secrets"] = {p: state[player]["secrets"][p] for p in ps}
        state1[player]["ignoreshare"] = {p: state[player]["ignoreshare"][p] for p in ps}
    return state1


def players_who_know_secret(state):
    knowers = set()
    for p in state:
        if state[p][1]:
            knowers.add(p)
    return knowers


def player_knows_secret_possibly_share(state):
    next_p = None
    state2 = copy_state(state)
    if players_who_know_secret(state) == {A, E1, I, E2, B}:
        for p in players_right_to_left():
            if state[p][0] == "locked":
                next_p = p
                break
        return next_p, state2
    for p in players_right_to_left():
        if state[p][1]:
            if not state[p][2]:
                next_p = p
                break
    if next_p is None:
        for p in state:
            if state2[p][0] == "locked":
                state2[p][0] = "expired"
    return next_p, state2


def share_secret_action(player):
    if player == A:
        return S_SA
    elif player == E1:
        return S_SE1
    elif player == I:
        return S_SI
    elif player == E2:
        return S_SE2
    elif player == B:
        return S_SB
    else:
        raise Exception("weird player")


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


def generate_routing_unlocking(player: Player, state, history):
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    global recursion_depth
    depth = len(history.split(";"))
    if depth > recursion_depth:
        recursion_depth = depth
    if final(state):
        return leaf5(*utility_leaf(state).utility)
    else:
        if all(state[player]["ignoreshare"].values()):
            raise Exception(f"It should not be player {player}'s turn, because they have ignored sharing secrets.")
        branch_actions = {}
        if state[player]["contract"] == "locked" and state[player]["secrets"][prev_player(player)]:
            # Action unlock
            state1 = copy_state(state)
            state1[player]["contract"] = "unlocked"
            state1[prev_player(player)]["secrets"][prev_player(player)] = True
            align_secret_knowledge(state1)
            if state1[prev_player(player)][2] == True:
                next_p, state2 = player_knows_secret_possibly_share(state1)
            else:
                next_p = prev_player(player)
                state2 = state1
            branch_actions[U] = generate_routing_unlocking(next_p, state2, history + str(player) + ".U;")
            # Ignoring unlock
            state3 = copy_state(state)
            state3[player][0] = "expired"
            for p in next_players(player):
                if state[p][0] == "locked":
                    state3[p][0] = "expired"
            # the next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p, state4 = player_knows_secret_possibly_share(state3)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state4, history + str(player) + ".I_U;")

        else:
            # Ignoring sharing
            state1 = copy_state(state)
            state1[player][2] = True
            next_p, state2 = player_knows_secret_possibly_share(state1)
            branch_actions[I_S] = generate_routing_unlocking(next_p, state2, history + str(player) + ".I_S;")
        # Sharing is caring
        for p in state:
            if not state[p][1]:
                state1 = copy_state(state)
                state1[p][1] = True
                next_p, state2 = player_knows_secret_possibly_share(state1)
                branch_actions[share_secret_action(p)] = generate_routing_unlocking(next_p, state2, history + str(player) + "." + str(share_secret_action(p)) + ";")
        return branch(player, branch_actions)

# state[p] = [<state of the contract>,<knowledge of secrets>,<igoresharing secrets>,<equivalence classes of secrets>]
# secrets are represented by players who wrote the HTCL contract with this hash
# ignoresharing with key p, means not sharing the secret that p used to lock their contract with anyone


initial_state = {
    "eq_secrets":  {{p for p in ps}},
    "time_orderings": None,
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
        "secrets": {A: False, E1: False, I: False, E2: False, B: True},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}}
}

intermediate_state = {
    "eq_secrets":  {{p for p in ps}},
    "time_orderings": None,
    A: {"contract": "null",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E1: {"contract": "locked",
         "secrets": {A: False, E1: False, I: False, E2: False, B: False},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    I: {"contract": "locked",
        "secrets": {A: False, E1: False, I: False, E2: False, B: False},
        "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    E2: {"contract": "expired",
         "secrets": {A: True, E1: True, I: True, E2: True, B: True},
         "ignoreshare": {A: False, E1: False, I: False, E2: False, B: False}},
    B: {"contract": "unlocked",
        "secrets": {A: True, E1: True, I: True, E2: True, B: True},
        "ignoreshare": {A: True, E1: True, I: True, E2: True, B: True}}
}


unlocking_tree = generate_routing_unlocking(B, initial_state, "")
# my_tree = generate_routing_unlocking(E2, intermediate_state)

tree(unlocking_tree)

finish()
