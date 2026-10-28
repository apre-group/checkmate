# Verdict-preserving game transforms for metamorphic fuzzing.
# Each returns (new_game, action_map, unchanged_props): action_map renames history actions,
# unchanged_props are the properties whose verdicts must stay the same.

import copy
import re

from gen_game import lin_term
from gen_cefg import declare, declared, map_history, utility_tuples

ALL_PROPS = {"weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"}
IDENT = re.compile(r"[A-Za-z_]\w*")


def nodes(tree):
    yield tree
    for c in tree.get("children", []) + tree.get("condition", []):
        yield from nodes(c["child"])


def leaves(tree):
    return [n for n in nodes(tree) if "utility" in n]


def utilities(game):
    """The utility lists of the leaves and of the honest utilities (of CEFGs, given without honest history)."""
    for l in leaves(game["tree"]):
        yield l["utility"]
    for h in game.get("honest_utilities", []):
        yield from utility_tuples(h["utility"])


def conditions(game):
    """The places of conditions in a CEFG, as (dict, key): condition nodes, honest histories and honest utilities."""
    for n in nodes(game["tree"]):
        for c in n.get("condition", []):
            yield c, "constraint"

    def history(h):
        for e in h:
            if not isinstance(e, str):
                for c in e:
                    yield c, "condition"
                    yield from history(c["path"])

    def utility(element):
        if element and "condition" in element[0]:
            for e in element:
                yield e, "condition"
                yield from utility(e["utility"])
    for h in game["honest_histories"]:
        yield from history(h)
    for h in game.get("honest_utilities", []):
        yield from utility(h["utility"])


def rename_players(game, rng):
    g = copy.deepcopy(game)
    old = sorted(g["players"])
    new = ["P", "Q", "R", "S", "T", "U"][:len(old)]
    # A non-identity permutation, so the alphabetical (index) order of players changes.
    while True:
        perm = rng.sample(new, len(new))
        if perm != new:
            break
    m = dict(zip(old, perm))
    g["players"] = [m[p] for p in g["players"]]
    for n in nodes(g["tree"]):
        if "player" in n:
            n["player"] = m[n["player"]]
    for us in utilities(g):
        for u in us:
            u["player"] = m[u["player"]]
    return g, {}, ALL_PROPS


def permute_children(game, rng):
    g = copy.deepcopy(game)
    for n in nodes(g["tree"]):
        if "children" in n:
            rng.shuffle(n["children"])
        if "condition" in n:
            rng.shuffle(n["condition"])
    return g, {}, ALL_PROPS


def rename_actions(game, rng):
    g = copy.deepcopy(game)
    new = ["m%d" % i for i in range(len(g["actions"]))]
    rng.shuffle(new)
    m = dict(zip(g["actions"], new))
    g["actions"] = [m[a] for a in g["actions"]]
    for n in nodes(g["tree"]):
        for c in n.get("children", []):
            c["action"] = m[c["action"]]
    g["honest_histories"] = [map_history(h, m.get) for h in g["honest_histories"]]
    return g, m, ALL_PROPS


def rename_symbols(game, rng):
    g = copy.deepcopy(game)
    known, unknown = declared(g["constants"])
    syms = known + unknown + g["infinitesimals"]
    new = ["v%d" % i for i in range(len(syms))]
    rng.shuffle(new)
    m = dict(zip(syms, new))

    def ren(expr):
        return IDENT.sub(lambda t: m.get(t.group(0), t.group(0)), str(expr))

    known, unknown = [m[c] for c in known], [m[c] for c in unknown]
    g["infinitesimals"] = [m[e] for e in g["infinitesimals"]]
    rng.shuffle(known)
    rng.shuffle(unknown)
    g["constants"] = declare(known, unknown)
    g["initial_constraints"] = [ren(c) for c in g["initial_constraints"]]
    g["property_constraints"] = {p: [ren(c) for c in cs] for p, cs in g["property_constraints"].items()}
    for us in utilities(g):
        for u in us:
            u["value"] = ren(u["value"])
    for d, k in conditions(g):
        d[k] = ren(d[k])
    for n in nodes(g["tree"]):
        if "reveals" in n:
            n["reveals"] = [m[r] for r in n["reveals"]]
    return g, {}, ALL_PROPS


def scale_utilities(game, rng):
    g = copy.deepcopy(game)
    k = rng.choice([2, 3, 5])
    for us in utilities(g):
        for u in us:
            u["value"] = "%d*(%s)" % (k, u["value"])
    return g, {}, ALL_PROPS


def shift_player(game, rng):
    # Comparisons in collusion resilience and practicality involve a player's utility on
    # both sides, so adding the same term everywhere cancels; weak immunity compares with 0.
    g = copy.deepcopy(game)
    p = rng.choice(g["players"])
    # only known constants: every leaf may use them
    term = lin_term(rng, declared(g["constants"])[0], 2, 3)
    for us in utilities(g):
        for u in us:
            if u["player"] == p:
                u["value"] = "(%s) + (%s)" % (u["value"], term)
    return g, {}, {"collusion_resilience", "practicality"}


TRANSFORMS = [rename_players, permute_children, rename_actions, rename_symbols,
              scale_utilities, shift_player]


def random_transform(game, rng):
    """Compose 1-3 random transforms."""
    names, action_map, props = [], {}, set(ALL_PROPS)
    for t in rng.sample(TRANSFORMS, rng.randint(1, 3)):
        game, m, p = t(game, rng)
        names.append(t.__name__)
        action_map = {a: m.get(b, b) for a, b in action_map.items()} if action_map else m
        props &= p
    return game, names, action_map, props
