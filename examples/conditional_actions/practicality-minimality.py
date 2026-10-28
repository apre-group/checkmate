# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
A small game in which practicality depends on the minimality of the sets of best choices
(property (M) of rationalizable families, the formula min in ComputeDom).

A can follow the honest action hon (utility 2 for A) or deviate. After deviating, C chooses between
    p: (3 for A, 2 for C)   and   q,
and after q, B chooses between
    l: (0 for A, 1 for B, 1 for C)   and   r: (0 for A, 0 for B, 3 for C).
B strictly prefers l, so the only rationalizable choice of B is {l}: C then gets 1 after q and prefers p,
where A gets 3 > 2. The deviation is profitable and the game is not practical.

The set {l, r} also contains a best choice of B, but it is not minimal. If it were allowed, C could hope for 3
after q, prefer q, and A would get 0 after deviating, so the game would wrongly be practical.

The unknown constant y is never revealed and occurs nowhere: it only makes every branch node have unknowns,
since without unknowns only single best choices are considered and minimality is not checked separately.

Expected result: NO, the game is not practical.
"""

A, B, C = PLAYERS = players('A', 'B', 'C')
hon, dev, p, q, l, r = ACTIONS = actions('hon', 'dev', 'p', 'q', 'l', 'r')
INFINITESIMALS = []
y, = UNKNOWN_CONSTANTS = unknown_constants('y')
CONSTANTS = UNKNOWN_CONSTANTS

INITIAL_CONSTRAINTS = []
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

HONEST_HISTORIES = [[hon]]
HONEST_UTILITIES = []

TREE = branch(A, {
    hon: leaf({A: 2, B: 0, C: 0}),
    dev: branch(C, {
        p: leaf({A: 3, B: 0, C: 2}),
        q: branch(B, {
            l: leaf({A: 0, B: 1, C: 1}),
            r: leaf({A: 0, B: 0, C: 3})
        })
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
