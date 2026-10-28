# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
A game in which B has to break a tie depending on a revealed value, but is only indifferent on part of the domain.

A can follow the honest action hon (utility 0 for A) or deviate. After deviating, A chooses without knowing x0, x1
between safe (utility -1) and risk0, risk1. Risk i reveals xi, and B chooses between
    li: (xi for A)   and   ri: (-xi for A),
where B gets 0 from both for xi >= 0 (indifferent) and 1 from li, 0 from ri for xi < 0 (B strictly prefers li).
The constants x0, x1 are unknown at the start and range over the reals.

For xi < 0, B plays li and A gets xi < 0. For xi >= 0, B has to play ri, so that A gets -xi <= 0; then deviating is
not profitable. Playing li for some xi > 0 would give A xi > 0. Practicality only needs some rationalizable way of
breaking the ties, so the game is practical.

As in sign-2, the selectors occur in hit and min of A's branch after dev and cannot be replaced by quantifiers.
Z3 does not decide the final check within its timeout; cvc5 synthesizes the selectors.

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


# risk i reveals xi; B is indifferent for xi >= 0 and prefers li for xi < 0
def after_risk(x, l, r):
    return condition({
        x >= 0: branch(B, {l: leaf({A: x, B: 0}), r: leaf({A: 0 - x, B: 0})}),
        x < 0: branch(B, {l: leaf({A: x, B: 1}), r: leaf({A: 0 - x, B: 0})})
    }, reveals=[x])


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
