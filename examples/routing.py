from dsl import *

A, E1, I, E2, B = players('A', 'E1', 'I', 'E2', 'B')
S_H, L, U, J, S_S, L_T, L_H, L_A, S_SE1 = actions(
    'S_H', 'L', 'U', 'J', 'S_S', 'L_T', 'L_H', 'L_A', 'S_SE1'
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


def leaf5(a: Expr, b: Expr, c: Expr, d: Expr, e: Expr) -> Leaf:
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
serifS_1 = todo
serifS_2 = todo
serifS_3 = todo
serifS_4 = todo
boldS_1 = todo
boldS_2 = todo
boldS_3 = todo
boldS_4 = todo


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
                                J: todo,
                                S_S: mathfracS_3,
                                S_SE1: todo,
                                U: branch(I, {
                                    J: todo,
                                    S_S: mathfracS_4,
                                    U: branch(E1, {
                                        J: leaf5(m + f + f+ f + rho - epsilon, - m - f - f, f, f, rho),
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