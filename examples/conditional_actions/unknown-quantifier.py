# import the dsl and add the parent directory to the path to be able to import it
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from dsl import *

"""
Small games for the quantifier at condition nodes in ComputeCWI and ComputeCCR.

At a condition node, the algorithms have to quantify over all constants that are unknown there, not only over the
ones revealed there. In all games, a condition node reveals x, and z is never revealed. If the initial constraints
relate them (x = z), quantifying only x leaves z free in the result, so that a player's choice above the condition
node could depend on the unknown z.

Running this script writes the five games as JSON files next to it:

unknown-quantifier-wi-linked.json, IC x = z:
    B plays the honest h or deviates; after d, A chooses a (utility x for A) or b (utility -x for A),
    and then x is revealed. A does not know x when choosing.
    Expected: NO, not weak immune (for A). Quantifying only x would give z >= 0 for a and z <= 0 for b,
    and their disjunction holds.
unknown-quantifier-wi-unlinked.json: the same game without initial constraints.
    Expected: NO, not weak immune.
unknown-quantifier-wi-holds.json, IC x = z: the same game, but a gives A x * x and b gives -1.
    Expected: YES, weak immune (A plays a).
unknown-quantifier-cr-linked.json, IC x = z:
    A plays the honest h (utilities 0, 0) or deviates; after d, B chooses a (A gets x, B gets -x) or b (A gets -x,
    B gets x), and then x is revealed. B does not know x when choosing, so A can gain by deviating.
    Expected: NO, not collusion resilient (and not weak immune for B).
unknown-quantifier-cr-unlinked.json: the same game without initial constraints.
    Expected: NO, not collusion resilient.
"""

A, B = PLAYERS = players('A', 'B')
h, d, a, b = ACTIONS = actions('h', 'd', 'a', 'b')
INFINITESIMALS = []
x, z = UNKNOWN_CONSTANTS = unknown_constants('x', 'z')
CONSTANTS = UNKNOWN_CONSTANTS

HONEST_HISTORIES = [[h]]
HONEST_UTILITIES = []


def reveal_x(utility_a, utility_b):
    """a condition node revealing x, with the same leaf below both edges"""
    return condition({
        x >= 0: leaf({A: utility_a, B: utility_b}),
        x < 0: leaf({A: utility_a, B: utility_b})
    })


def wi_tree(utility_a, utility_b):
    """B moves first (honest: h); after d, A chooses a or b without knowing x"""
    return branch(B, {
        h: leaf({A: 0, B: 0}),
        d: branch(A, {
            a: reveal_x(utility_a, 0),
            b: reveal_x(utility_b, 0)
        })
    })


def cr_tree():
    """A moves first (honest: h); after d, B chooses a or b without knowing x"""
    return branch(A, {
        h: leaf({A: 0, B: 0}),
        d: branch(B, {
            a: reveal_x(x, -x),
            b: reveal_x(-x, x)
        })
    })


GAMES = {
    'wi-linked': (wi_tree(x, -x), [x == z]),
    'wi-unlinked': (wi_tree(x, -x), []),
    'wi-holds': (wi_tree(x * x, -1), [x == z]),
    'cr-linked': (cr_tree(), [x == z]),
    'cr-unlinked': (cr_tree(), []),
}

for name, (tree, initial_constraints) in GAMES.items():
    path = Path(__file__).parent / f'unknown-quantifier-{name}.json'
    with open(path, 'w') as file:
        finish(
            PLAYERS,
            ACTIONS,
            INFINITESIMALS,
            CONSTANTS,
            initial_constraints,
            [],
            [],
            [],
            [],
            HONEST_HISTORIES,
            HONEST_UTILITIES,
            tree,
            file=file
        )
