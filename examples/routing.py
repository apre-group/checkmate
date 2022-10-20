from dsl import *
from typing import Union
import copy

A, E1, I, E2, B = players('A', 'E1', 'I', 'E2', 'B')
S_H, L, U, J, S_S, L_T, L_H, L_A, S_SE1, S_SI, I_L, I_U, I_S = actions(
    'S_H', 'L', 'U', 'J', 'S_S', 'L_T', 'L_H', 'L_A', 'S_SE1', 'S_SI', 'I_L', 'I_U', 'I_S'
)
epsilon, rho, todoo = infinitesimals('epsilon', 'rho', 'todo')
m, f = constants('m', 'f')

initial_constraints(
    rho > 0,
    epsilon > 0,
    f > 0,
    m > f
)

weak_immunity_constraints()
collusion_resilience_constraints()
practicality_constraints()

honest_histories((S_H, L, L, L, L, U, U, U, U))


def leaf5(a: LExpr, b: LExpr, c: LExpr, d: LExpr, e: LExpr) -> Leaf:
    return leaf({A: a, E1: b, I: c, E2: d, B: e})


todo = leaf5(todoo, todoo, todoo, todoo, todoo)


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
        ps = [x for x in value[2]]
        state1[key] = [value[0], value[1], ps]
    return state1


def player_knows_secret_possibly_share(state):
    next_p = None
    state2 = copy_state(state)
    for p in players_right_to_left():
        if state[p][1]:
            if not ({q for q in state.keys() if not state[q][1]}.issubset(set(state[p][2]))):
                next_p = p
                break
    if next_p is None:
        for p in state:
            if state2[p][0] == "locked":
                state2[p][0] = "expired"
    return next_p, state2


def generate_routing_unlocking(player: Player, state):
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    if final(state):
        return leaf5(*utility_leaf(state).utility)
    else:
        branch_actions = {}
        if state[player][0] == "locked":
            # Action unlock
            state1 = copy_state(state)
            state1[player][0] = "unlocked"
            state1[prev_player(player)][1] = True
            branch_actions[U] = generate_routing_unlocking(prev_player(player), state1)
            # Ignoring unlock
            state2 = copy_state(state)
            state2[player][0] = "expired"
            for p in next_players(player):
                if state[p][0] == "locked":
                    state2[p][0] = "expired"
            # teh next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p, state2 = player_knows_secret_possibly_share(state)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state2)
        else:
            # Ignoring sharing
            state1 = copy_state(state)
            ps = [A, E1, I, E2, B]
            ps.remove(player)
            state1[player][2] = ps
            next_p, state2 = player_knows_secret_possibly_share(state1)
            branch_actions[I_S] = generate_routing_unlocking(next_p, state2)
            # Sharing is caring

        return branch(player, branch_actions)


initial_state = {
    A: ("null", False, []),
    E1: ("locked", False, []),
    I: ("locked", False, []),
    E2: ("locked", False, []),
    B: ("locked", True, []),
}

intermediate_state = {
    A: ("null", False, []),
    E1: ("locked", False, []),
    I: ("locked", False, []),
    E2: ("expired", True, []),
    B: ("unlocked", True, [A, E1, I, E2]),
}

# unlocking_tree = generate_routing_unlocking(B, initial_state)
my_tree = generate_routing_unlocking(E2, intermediate_state)

tree(my_tree)

finish()
