from dsl import *
from typing import Union

A, E1, I, E2, B = players('A', 'E1', 'I', 'E2', 'B')
S_H, L, U, J, S_S, L_T, L_H, L_A, S_SE1, S_SI = actions(
    'S_H', 'L', 'U', 'J', 'S_S', 'L_T', 'L_H', 'L_A', 'S_SE1', 'S_SI'
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
