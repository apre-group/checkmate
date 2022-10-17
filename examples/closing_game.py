#!/usr/bin/env python3

from dsl import *

pA, pB = players('A', 'B')
H, D, C_h, C_c, S, I, P, Up, Um, A = actions(
    'H', 'D', 'C_h', 'C_c', 'S', 'I', 'P', 'U+', 'U-', 'A'
)
alpha, epsilon, rho = infinitesimals('alpha', 'epsilon', 'rho')
a, b, c, f, d_A, d_B, p_A, p_B = constants(
    'a', 'b', 'c', 'f', 'd_A', 'd_B', 'p_A', 'p_B'
)

initial_constraints(
    alpha > epsilon,
    epsilon > rho,
    rho > 0,
    a > 0,
    b > 0,
    c > 0,
    f > 0,
    d_A > 0,
    d_B > 0,
    p_A > 0,
    p_B > 0,
    a >= d_B,
    b >= d_A,
    a >= p_B,
    b >= p_A,
    b >= c
)

weak_immunity_constraints(a >= f, b >= f)
collusion_resilience_constraints(a - p_B + d_A >= f, b - p_A + d_B >= f)
practicality_constraints(a - p_B + d_A >= f, b - p_A + d_B >= f, c != p_A)

honest_histories((H,), (C_h, S))

def leaf2(a: Expr, b: Expr) -> Leaf:
    return leaf({pA: a, pB: b})

tree(
    branch(pA, {
        H: leaf2(alpha - epsilon, alpha),
        C_h: branch(pB, {
            Up: branch(pA, {
                H: leaf2(alpha - epsilon, alpha),
                I: branch(pB, {
                    D: branch(pA, {
                        P: leaf2(b - f + alpha, -b),
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
                    }),
                    I: leaf2(-a, -b),
                    H: leaf2(alpha, alpha - epsilon),
                    S: leaf2(alpha, alpha)
                }),
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                }),
                A: branch(pB, {
                    S: leaf2(-p_A + rho + alpha, p_A + rho + alpha),
                    H: leaf2(rho + alpha, rho + alpha - epsilon),
                    D: branch(pA, {
                        I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon),
                        P: leaf2(b - p_A - f + rho + alpha, -b + p_A + rho)
                    }),
                    I: branch(pA, {
                        I: leaf2(-a - p_A + rho, -b + p_A + rho),
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            P: leaf2(-a - p_A + rho, a + p_A - f + rho + alpha),
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha)
                        })
                    })
                })
            }),
            Um: branch(pA, {
                H: leaf2(alpha - epsilon, alpha),
                I: branch(pB, {
                    D: branch(pA, {
                        P: leaf2(b - f + alpha, -b),
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
                    }),
                    I: leaf2(-a, -b),
                    H: leaf2(alpha, alpha - epsilon),
                    S: leaf2(alpha, alpha)
                }),
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                }),
                A: branch(pB, {
                    S: leaf2(p_B + rho + alpha, -p_B + rho + alpha),
                    H: leaf2(rho + alpha, rho + alpha - epsilon),
                    D: branch(pA, {
                        I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon),
                        P: leaf2(b + p_B - f + rho + alpha, -b - p_B + rho)
                    }),
                    I: branch(pA, {
                        I: leaf2(-a + p_B + rho, -b - p_B + rho),
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            P: leaf2(-a + p_B + rho, a - p_B - f + rho + alpha),
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha)
                        })
                    })
                })
            }),
            I: branch(pA, {
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                }),
                Up: branch(pB, {
                    H: leaf2(alpha, alpha - epsilon),
                    I: branch(pA, {
                        D: branch(pB, {
                            P: leaf2(-a, a - f + alpha),
                            I: leaf2(d_A + alpha - epsilon, -d_A + alpha)
                        }),
                        I: leaf2(-a, -b),
                        H: leaf2(alpha - epsilon, alpha)
                    }),
                    S: leaf2(alpha, alpha),
                    D: branch(pA, {
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon),
                        P: leaf2(b - f + alpha, -b)
                    }),
                    A: branch(pA, {
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha),
                            P: leaf2(-a - p_A + rho, a + p_A - f + rho + alpha)
                        }),
                        I: branch(pB, {
                            S: leaf2(-p_A + rho + alpha, p_A + rho + alpha),
                            I: leaf2(-a - p_A + rho, -b + p_A + rho),
                            H: leaf2(rho + alpha, rho + alpha - epsilon),
                            D: branch(pA, {
                                P: leaf2(b - p_A - f + rho + alpha, -b + p_A + rho),
                                I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon)
                            })
                        })
                    })
                }),
                Um: branch(pB, {
                    H: leaf2(alpha, alpha - epsilon),
                    I: branch(pA, {
                        D: branch(pB, {
                            P: leaf2(-a, a - f + alpha),
                            I: leaf2(d_A + alpha - epsilon, -d_A + alpha)
                        }),
                        I: leaf2(-a, -b),
                        H: leaf2(alpha - epsilon, alpha)
                    }),
                    S: leaf2(alpha, alpha),
                    D: branch(pA, {
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon),
                        P: leaf2(b - f + alpha, -b)
                    }),
                    A: branch(pA, {
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha),
                            P: leaf2(-a + p_B + rho, a - p_B - f + rho + alpha)
                        }),
                        I: branch(pB, {
                            S: leaf2(p_B + rho + alpha, -p_B + rho + alpha),
                            I: leaf2(-a + p_B + rho, -b - p_B + rho),
                            H: leaf2(rho + alpha, rho + alpha - epsilon),
                            D: branch(pA, {
                                P: leaf2(b + p_B - f + rho + alpha, -b - p_B + rho),
                                I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon)
                            })
                        })
                    })
                }),
                I: leaf2(-a, -b),
                H: leaf2(alpha - epsilon, alpha)
            }),
            S: leaf2(alpha, alpha),
            D: branch(pA, {
                P: leaf2(b - f + alpha, -b),
                I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
            }),
            H: leaf2(alpha, alpha - epsilon)
        }),
        D: branch(pB, {
            I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
            P: leaf2(-a, a - f + alpha)
        }),
        C_c: branch(pB, {
            H: leaf2(alpha, alpha - epsilon),
            D: branch(pA, {
                P: leaf2(b - f + alpha, -b),
                I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
            }),
            S: leaf2(c + alpha, -c + alpha),
            I: branch(pA, {
                H: leaf2(alpha - epsilon, alpha),
                I: leaf2(-a, -b),
                Um: branch(pB, {
                    H: leaf2(alpha, alpha - epsilon),
                    I: branch(pA, {
                        D: branch(pB, {
                            P: leaf2(-a, a - f + alpha),
                            I: leaf2(d_A + alpha - epsilon, -d_A + alpha)
                        }),
                        I: leaf2(-a, -b),
                        H: leaf2(alpha - epsilon, alpha)
                    }),
                    S: leaf2(c + alpha, -c + alpha),
                    D: branch(pA, {
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon),
                        P: leaf2(b - f + alpha, -b)
                    }),
                    A: branch(pA, {
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha),
                            P: leaf2(-a + p_B + rho, a - p_B - f + rho + alpha)
                        }),
                        I: branch(pB, {
                            S: leaf2(c + p_B + rho + alpha, -c - p_B + rho + alpha),
                            I: leaf2(-a + p_B + rho, -b - p_B + rho),
                            H: leaf2(rho + alpha, rho + alpha - epsilon),
                            D: branch(pA, {
                                P: leaf2(b + p_B - f + rho + alpha, -b - p_B + rho),
                                I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon)
                            })
                        })
                    })
                }),
                Up: branch(pB, {
                    H: leaf2(alpha, alpha - epsilon),
                    I: branch(pA, {
                        D: branch(pB, {
                            P: leaf2(-a, a - f + alpha),
                            I: leaf2(d_A + alpha - epsilon, -d_A + alpha)
                        }),
                        I: leaf2(-a, -b),
                        H: leaf2(alpha - epsilon, alpha)
                    }),
                    S: leaf2(c + alpha, -c + alpha),
                    D: branch(pA, {
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon),
                        P: leaf2(b - f + alpha, -b)
                    }),
                    A: branch(pA, {
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha),
                            P: leaf2(-a - p_A + rho, a + p_A - f + rho + alpha)
                        }),
                        I: branch(pB, {
                            S: leaf2(c - p_A + rho + alpha, -c + p_A + rho + alpha),
                            I: leaf2(-a - p_A + rho, -b + p_A + rho),
                            H: leaf2(rho + alpha, rho + alpha - epsilon),
                            D: branch(pA, {
                                P: leaf2(b - p_A - f + rho + alpha, -b + p_A + rho),
                                I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon)
                            })
                        })
                    })
                }),
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, - d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                })
            }),
            Um: branch(pA, {
                H: leaf2(alpha - epsilon, alpha),
                I: branch(pB, {
                    D: branch(pA, {
                        P: leaf2(b - f + alpha, -b),
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
                    }),
                    I: leaf2(-a, -b),
                    H: leaf2(alpha, alpha - epsilon),
                    S: leaf2(c + alpha, -c + alpha)
                }),
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                }),
                A: branch(pB, {
                    S: leaf2(c + p_B + rho + alpha, -c - p_B + rho + alpha),
                    H: leaf2(rho + alpha, rho + alpha - epsilon),
                    D: branch(pA, {
                        I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon),
                        P: leaf2(b + p_B - f + rho + alpha, -b - p_B + rho)
                    }),
                    I: branch(pA, {
                        I: leaf2(-a + p_B + rho, -b - p_B + rho),
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            P: leaf2(-a + p_B + rho, a - p_B - f + rho + alpha),
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha)
                        })
                    })
                })
            }),
            Up: branch(pA, {
                H: leaf2(alpha - epsilon, alpha),
                I: branch(pB, {
                    D: branch(pA, {
                        P: leaf2(b - f + alpha, -b),
                        I: leaf2(-d_B + alpha, d_B + alpha - epsilon)
                    }),
                    I: leaf2(-a, -b),
                    H: leaf2(alpha, alpha - epsilon),
                    S: leaf2(c + alpha, -c + alpha)
                }),
                D: branch(pB, {
                    I: leaf2(d_A + alpha - epsilon, -d_A + alpha),
                    P: leaf2(-a, a - f + alpha)
                }),
                A: branch(pB, {
                    S: leaf2(c - p_A + rho + alpha, -c + p_A + rho + alpha),
                    H: leaf2(rho + alpha, rho + alpha - epsilon),
                    D: branch(pA, {
                        I: leaf2(-d_B + rho + alpha, d_B + rho + alpha - epsilon),
                        P: leaf2(b - p_A - f + rho + alpha, -b + p_A + rho)
                    }),
                    I: branch(pA, {
                        I: leaf2(-a - p_A + rho, -b + p_A + rho),
                        H: leaf2(rho + alpha - epsilon, rho + alpha),
                        D: branch(pB, {
                            P: leaf2(-a - p_A + rho, a + p_A - f + rho + alpha),
                            I: leaf2(d_A + rho + alpha - epsilon, -d_A + rho + alpha)
                        })
                    })
                })
            })
        })
    })
)

finish()
