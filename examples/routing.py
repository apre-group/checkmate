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


def generate_routing_unlocking(player, state):
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    if final(state):
        return leaf5(*utility_leaf(state).utility)
    else:
        branch_actions = {}
        if state[player][0] == "locked":
            # Action unlock
            state1 = copy.deepcopy(state)
            state1[player][0] = "unlocked"
            state1[prev_player(player)][1] = True
            branch_actions[U] = generate_routing_unlocking(prev_player(player), state1)
            # Ignoring unlock
            state2 = copy.deepcopy(state)
            state2[player][0] = "expired"
            for p in next_players(player):
                if state[p][0] == "locked":
                    state2[p][0] = "expired"
            # teh next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p = None
            for p in players_right_to_left():
                if state[p][1]:
                    if not ({q for q in state.keys() if not state[q][1]}.issubset(set(state[p][2]))):
                        next_p = p
                        break
            if next_p is None:
                for p in state:
                    if state2[p][0] == "locked":
                        state2[p][0] = "expired"
            branch_actions[I_U] = generate_routing_unlocking(next_p, state2)
        return branch(player, branch_actions)


initial_state = {
    A : ("null", False, []),
    E1 : ("locked", False, []),
    I : ("locked", False, []),
    E2 : ("locked", False, []),
    B : ("locked", True, []),
}

intermediate_state = {
    A : ("null", False, []),
    E1 : ("unlocked", False, []),
    I : ("expired", False, []),
    E2 : ("unlocked", False, []),
    B : ("unlocked", True, []),
}

unlocking_tree = generate_routing_unlocking(B, initial_state)

mathbbS_1 = todo
mathbbS_2 = todo
mathbbS_3 = todo
mathbbS_4 = todo
mathfracS_1 = todo
mathfracS_2 = todo
mathfracS_3 = todo
mathfracS_4 = todo

mathfracS_5 = branch(E1, {
    J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
    U: branch(B, {
        J: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho),
        S_SI: branch(I, {
            J: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho),
            U: leaf5(rho, f, m+f+f-epsilon, -m, rho)
        })
    }),
    S_SI: branch(I, {
        J: branch(E1, {
            J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
            U: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho)
        }),
        U: branch(E1, {
            J: leaf5(m+f+f+f+rho-epsilon, -m-f-f, m+f+f-epsilon, -m, rho),
            U: leaf5(rho, f, m+f+f-epsilon, -m, rho)
        })
    })
})

mathfracS_6 = branch(E1, {
    J: leaf5(m+f+f+f+rho-epsilon, -epsilon, epsilon, -m, rho),
    U: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho)
})

serifS_1 = todo
serifS_2 = todo
serifS_3 = todo
serifS_4 = todo
boldS_1 = todo
boldS_2 = todo
boldS_3 = todo
boldS_4 = todo

wormhole = branch(E1, {
            J: leaf5(m + f + f + f + rho - epsilon, - epsilon, - epsilon, - m, rho),
            U: branch(B, {
                J: leaf5(rho, m + f + f + f - epsilon, - epsilon, - m, rho),
                S_SI: branch(I, {
                    J: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho),
                    U: leaf5(rho, f,m+f+f-epsilon, -m, rho)
                })
            }),
            S_SI: branch(I, {
                J: branch(E1, {
                    J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
                    U: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho)
                }),
                U: branch(E1, {
                    J: leaf5(m+f+f+f+rho-epsilon, -m-f-f, m+f+f-epsilon, -m, rho),
                    U: leaf5(rho, f, m+f+f-epsilon, -m, rho)
                })
            })
        })


tree(
    branch(B, {
        J: leaf5(0, 0, 0, 0, 0),
        S_S: mathfracS_1,
        S_H: branch(A, {
            J: leaf5(0, 0, 0, 0, 0),
            L_A: mathbbS_1,
            L_T: boldS_1,
            L_H: serifS_1,
            L: branch(E1, {
                J: leaf5(- epsilon, 0, 0, 0, 0),
                L_A: mathbbS_2,
                L_H: serifS_2,
                L_T: boldS_2,
                L: branch(I, {
                    J: leaf5(- epsilon, - epsilon, 0, 0, 0),
                    L_A: mathbbS_3,
                    L_H: serifS_3,
                    L_T: boldS_3,
                    L: branch(E2, {
                        J: leaf5(- epsilon, - epsilon, - epsilon, 0, 0),
                        L_A: mathbbS_4,
                        L_H: serifS_4,
                        L_T: boldS_4,
                        L: branch(B, {
                            J: leaf5(- epsilon, - epsilon, - epsilon, - epsilon, 0),
                            S_S: mathfracS_2,
                            U: branch(E2, {
                                J: branch(B, {
                                    J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
                                    S_SE1: mathfracS_5,
                                    S_SI: branch(I, {
                                        S_SE1: mathfracS_6,
                                        U: branch(E1, {
                                            J: leaf5(m+f+f+f+rho-epsilon, -m-f-f, m+f+f-epsilon, -m, rho),
                                            U: leaf5(rho, f, m+f+f+epsilon, -m, rho)
                                        }),
                                        J: branch(B, {
                                            J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
                                            S_SE1: branch(E1, {
                                                J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -epsilon, -m, rho),
                                                U: leaf5(rho, m+f+f+f-epsilon, -epsilon, -m, rho)
                                            })
                                        })
                                    })
                                }),
                                S_S: mathfracS_3,
                                S_SE1: wormhole,
                                U: branch(I, {
                                    J: branch(E2, {
                                        S_SE1: branch(E1, {
                                            J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -m-f, f, rho),
                                            U: leaf5(rho, m+f+f+f-epsilon, -m-f, f, rho)
                                        }),
                                        J: branch(B, {
                                            J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -m-f, f, rho),
                                            S_SE1: branch(E1, {
                                                J: leaf5(m+f+f+f+rho-epsilon, -epsilon, -m-f, f, rho),
                                                U: leaf5(rho, m+f+f+f-epsilon, -m-f, f, rho)
                                            })
                                        }),
                                    }),
                                    S_S: mathfracS_4,
                                    U: branch(E1, {
                                        J: leaf5(m + f + f + f + rho - epsilon, - m - f - f, f, f, rho),
                                        U: leaf5(rho, f, f, f, rho)
                                    })
                                })
                            })
                        })
                    })
                })
            })

        })
    }
    ))


finish()
