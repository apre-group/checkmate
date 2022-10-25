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
    for p in state:
        if state[p][0] == "locked":
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
    if state[B][0] == "unlocked":
        ut = ut + Utility_leaf((rho+m+3*f,0,0,-m,rho))
    elif state[B][0] == "expired":
        ut = ut + Utility_leaf((0,0,0,-epsilon,0))
    if state[E2][0] == "unlocked":
        ut = ut + Utility_leaf((0,0,-m-f,m+f,0))
    elif state[E2][0] == "expired":
        ut = ut + Utility_leaf((0,0,-epsilon,0,0))
    if state[I][0] == "unlocked":
        ut = ut + Utility_leaf((0,-m-2*f,m+2*f,0,0))
    elif state[I][0] == "expired":
        ut = ut + Utility_leaf((0,-epsilon,0,0,0))
    if state[E1][0] == "unlocked":
        ut = ut + Utility_leaf((-m-3*f,m+3*f,0,0,0))
    elif state[E1][0] == "expired":
        ut = ut + Utility_leaf((-epsilon,0,0,0,0))
    return ut


def copy_state(state):
    state1 = {}
    for key, value in state.items():
        state1[key] = [v for v in value]
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
        if state[player][2]:
            raise Exception(f"It should not be player {player}'s turn, because they have ignored sharing secrets.")
        branch_actions = {}
        if state[player][0] == "locked":
            # Action unlock
            state1 = copy_state(state)
            state1[player][0] = "unlocked"
            state1[prev_player(player)][1] = True
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


initial_state = {
    A: ["null", False, False],
    E1: ["locked", False, False],
    I: ["locked", False, False],
    E2: ["locked", False, False],
    B: ["locked", True, False],
}

intermediate_state = {
    A: ["null", False, False],
    E1: ["locked", False, False],
    I: ["locked", False, False],
    E2: ["expired", True, False],
    B: ["unlocked", True, True],
}

unlocking_tree = generate_routing_unlocking(B, initial_state, "")
# my_tree = generate_routing_unlocking(E2, intermediate_state)

tree(unlocking_tree)

finish()
