# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
A game in which B has to break a tie depending on a revealed value, as in the example for breaking ties depending on
revealed values in the paper, but A gambles before the values are revealed.

A can follow the honest action hon (utility 0 for A) or deviate. After deviating, A chooses without knowing x0, x1
between safe (utility -1) and risk0, risk1. Risk i reveals xi, and B chooses between
    li: (xi for A, 0 for B)   and   ri: (-xi for A, 0 for B),
so B is indifferent for every value of xi. The constants x0, x1 are unknown at the start and range over the reals.

If B plays li for xi <= 0 and ri for xi > 0, A gets -|xi| <= 0 after risk i, so deviating is not profitable.
A selection that does not depend on xi does not suffice (always li: xi = 1 gives A 1 > 0; always ri: xi = -1 does).
Practicality only needs some rationalizable way of breaking the ties, so the game is practical.

The selectors of the condition nodes occur in hit and min of A's branch after dev, under a universal and an
existential quantifier over the revealed constants, so they cannot be replaced by quantifiers. Z3 does not decide
the final check within its timeout; cvc5 synthesizes the selectors.

Expected result: YES, the game is practical (decided by cvc5).
"""

A, B = PLAYERS = players('A', 'B')
hon, dev, safe, risk0, risk1, l0, l1, r0, r1 = ACTIONS = actions('hon', 'dev', 'safe', 'risk0', 'risk1', 'l0', 'l1', 'r0', 'r1')
INFINITESIMALS = []
x0, x1 = UNKNOWN_CONSTANTS = unknown_constants('x0', 'x1')
CONSTANTS = UNKNOWN_CONSTANTS

INITIAL_CONSTRAINTS = []
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

HONEST_HISTORIES = [[hon]]
HONEST_UTILITIES = []


# risk i reveals xi, then B is indifferent between li and ri
def after_risk(x, l, r):
    return condition({Truth(): branch(B, {l: leaf({A: x, B: 0}), r: leaf({A: 0 - x, B: 0})})}, reveals=[x])


TREE = branch(A, {
    hon: leaf({A: 0, B: 0}),
    dev: branch(A, {
        safe: leaf({A: -1, B: 0}),
        risk0: after_risk(x0, l0, r0),
        risk1: after_risk(x1, l1, r1)
    })
})

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
    HONEST_UTILITIES,
    TREE
)
