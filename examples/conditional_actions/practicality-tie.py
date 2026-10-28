# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
A small game in which practicality depends on how a tie at a single value of an unknown is broken
(a variant of the example for computing rationalizable utility sets in the paper).

A can follow the honest action hon (utility 2 for A) or deviate. After deviating, A chooses without knowing y
between safe (utility 1) and risk. After risk, y is revealed. For y <= 2, B chooses between
    l: (4 - y for A, y for B)   and   r: (0 for A, 1 for B),
so B prefers r for y = 0, is indifferent for y = 1, and prefers l for y = 2; for y = 3 the game ends with 0 for A.
The constant y is unknown at the start and takes one of the values 0, 1, 2, 3 (initial constraints).

If B breaks the tie at y = 1 towards r, A's best outcome after deviating is 2 (l at y = 2), which is not better than
the honest 2: the deviation is not profitable. If B breaks it towards l, A can get 3 at y = 1.
Practicality only needs some rationalizable way of breaking the tie, so the game is practical.

The tie only matters because two rationalizable utility sets of B's subgame are needed to cover all values of y
(l for y >= 1, r for y <= 1), and the order in which they are tried decides the tie: this checks that a utility
is only live where no earlier candidate holds. The domain of y is finite on purpose: for real y, A would get
almost 3 for y slightly above 1, whatever B does at y = 1.

Expected result: YES, the game is practical.
"""

A, B = PLAYERS = players('A', 'B')
hon, dev, safe, risk, l, r = ACTIONS = actions('hon', 'dev', 'safe', 'risk', 'l', 'r')
INFINITESIMALS = []
y, = UNKNOWN_CONSTANTS = unknown_constants('y')
CONSTANTS = UNKNOWN_CONSTANTS

INITIAL_CONSTRAINTS = [disjunction(y == 0, y == 1, y == 2, y == 3)]
WEAK_IMMUNITY_CONSTRAINTS = []
WEAKER_IMMUNITY_CONSTRAINTS = []
COLLUSION_RESILIENCE_CONSTRAINTS = []
PRACTICALITY_CONSTRAINTS = []

HONEST_HISTORIES = [[hon]]
HONEST_UTILITIES = []

# risk reveals y
after_risk = condition(
    {
        y <= 2: branch(B, {
            l: leaf({A: 4 - y, B: y}),
            r: leaf({A: 0, B: 1})
        }),
        y > 2: leaf({A: 0, B: 0})
    },
    reveals=[y]
)

TREE = branch(A, {
    hon: leaf({A: 2, B: 0}),
    dev: branch(A, {
        safe: leaf({A: 1, B: 0}),
        risk: after_risk
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
