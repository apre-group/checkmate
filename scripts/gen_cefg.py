#!/usr/bin/env python3
# Random conditional game (CEFG) generator for fuzzing. Usage: gen_cefg.py [--seed S] [--embed] [-o out.json]
# Also embeds EFGs into CEFGs that must have the same verdicts, and has the helpers for walking CEFGs.

import argparse
import copy
import json
import random
import re
import sys

from gen_game import gen_constraint, gen_game, gen_utility, lin_term, satisfiable

PROPS = ["weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"]
IDENT = re.compile(r"[A-Za-z_]\w*")
# A condition "true" on the honest history makes checkmate fail with "Error: index out of bounds",
# so reveal-only nodes (a single condition "true") are only generated with this set.
TRUE_CONDITIONS = False


# ---- walking CEFGs ------------------------------------------------------------

def is_condition(node):
    return "condition" in node


def edges(node):
    """(step, child) for the children of a branch (step ("a", action)) or condition node (step ("c", index))."""
    if "children" in node:
        return [(("a", c["action"]), c["child"]) for c in node["children"]]
    if is_condition(node):
        return [(("c", i), c["child"]) for i, c in enumerate(node["condition"])]
    return []


def nodes(tree):
    yield tree
    for _, c in edges(tree):
        yield from nodes(c)


def node_at(tree, steps):
    for _, s in steps:
        tree = (next(c["child"] for c in tree["children"] if c["action"] == s) if "children" in tree
                else tree["condition"][s]["child"])
    return tree


def declared(decl):
    """(known, unknown) names of a constants or infinitesimals declaration: a list (all known) or {known, unknown}."""
    if isinstance(decl, dict):
        return list(decl.get("known", [])), list(decl.get("unknown", []))
    return list(decl), []


def declare(known, unknown):
    # a plain list without unknowns, as the EFG analysis only reads that
    return {"known": known, "unknown": unknown} if unknown else known


def revealed_at(node, unknowns):
    """The unknowns revealed at a condition node: those in its conditions and those it lists."""
    names = set(node.get("reveals", []))
    for c in node["condition"]:
        names |= set(IDENT.findall(c["constraint"]))
    return names & set(unknowns)


def follow_honest(tree, history, steps):
    """The rest of `history` at the end of `steps`, or None if `steps` leave the honest history."""
    node, rest = tree, history
    for kind, s in steps:
        if not rest:
            return None
        if kind == "a":
            if rest[0] != s:
                return None
            rest = rest[1:]
        else:
            constraint = node["condition"][s]["constraint"]
            entry = next((e for e in rest[0] if e["condition"] == constraint), None)
            if entry is None:
                return None
            rest = entry["path"]
        node = node_at(node, [(kind, s)])
    return rest


def truncate_honest(tree, history, steps):
    """`history` ending at the end of `steps` (which follow it)."""
    if not steps:
        return []
    (kind, s), rest = steps[0], steps[1:]
    child = node_at(tree, [steps[0]])
    if kind == "a":
        return [s] + truncate_honest(child, history[1:], rest)
    constraint = tree["condition"][s]["constraint"]
    return [[dict(e, path=truncate_honest(child, e["path"], rest)) if e["condition"] == constraint else e
             for e in history[0]]]


def honest_leaves(tree, history, conds=()):
    """(conditions, leaf) for every leaf the honest history ends in: it continues in every condition."""
    if "utility" in tree or "subtree" in tree:
        yield list(conds), tree
        return
    if "children" in tree:
        yield from honest_leaves(node_at(tree, [("a", history[0])]), history[1:], conds)
        return
    for e in history[0]:
        child = next(c["child"] for c in tree["condition"] if c["constraint"] == e["condition"])
        yield from honest_leaves(child, e["path"], conds + (e["condition"],))


def honest_utility(tree, history):
    """The honest utility at the end of `history` as in "honest_utilities": nested lists of {condition, utility}."""
    if "utility" in tree:
        return copy.deepcopy(tree["utility"])
    if "children" in tree:
        return honest_utility(node_at(tree, [("a", history[0])]), history[1:])
    return [{"condition": e["condition"],
             "utility": honest_utility(next(c["child"] for c in tree["condition"] if c["constraint"] == e["condition"]),
                                       e["path"])}
            for e in history[0]]


def utility_tuples(element):
    """The utility lists in an honest utility element."""
    if element and "condition" in element[0]:
        for e in element:
            yield from utility_tuples(e["utility"])
    else:
        yield element


def map_history(history, action=lambda a: a, condition=lambda c: c):
    return [action(e) if isinstance(e, str) else
            [{"condition": condition(c["condition"]), "path": map_history(c["path"], action, condition)} for c in e]
            for e in history]


# ---- genuine CEFGs --------------------------------------------------------------

# (weight, players, depth, max branching, chance to stop early at a leaf)
SIZES = {
    "small": (0.5, (2, 3), (2, 3), (2, 3), 0.3),
    "medium": (0.4, (2, 4), (3, 4), (2, 3), 0.25),
    "large": (0.1, (3, 5), (4, 5), (2, 3), 0.2),
}


def gen_conditions(rng, unknown, domains, known):
    """The conditions of a condition node on `unknown` (or, if None, on a known constant): mostly a partition."""
    if unknown is None:
        c = rng.choice(known)
        t = rng.randint(-1, 2)
        if rng.random() < 0.3:
            return ["%s < %d" % (c, t), "%s = %d" % (c, t), "%s > %d" % (c, t)]
        return ["%s >= %d" % (c, t), "%s < %d" % (c, t)]
    values = domains.get(unknown)
    if values and rng.random() < 0.6:
        # a partition of the finite domain into groups of values
        vals = rng.sample(values, len(values))
        k = rng.randint(2, len(vals))
        cuts = sorted(rng.sample(range(1, len(vals)), k - 1))
        groups = [vals[i:j] for i, j in zip([0] + cuts, cuts + [len(vals)])]
        return [" | ".join("%s = %d" % (unknown, v) for v in g) for g in groups]
    if known and rng.random() < 0.3:
        bound = lin_term(rng, known, 1, 2)
    else:
        bound = str(rng.randint(-1, 3))
    if rng.random() < 0.1:
        # overlapping conditions: both hold at the bound
        return ["%s >= %s" % (unknown, bound), "%s <= %s" % (unknown, bound)]
    return ["%s >= %s" % (unknown, bound), "%s < %s" % (unknown, bound)]


def gen_cefg(rng):
    size = rng.choices(list(SIZES), [w for w, *_ in SIZES.values()])[0]
    _, n_players, depth, branch, stop_rate = SIZES[size]
    players = ["A", "B", "C", "D", "E"][:rng.randint(*n_players)]
    known = ["c%d" % i for i in range(rng.randint(1, 2))]
    unknowns = ["u%d" % i for i in range(rng.choice([0, 1, 1, 2, 2]))]
    infinitesimals = ["e%d" % i for i in range(rng.choice([0, 0, 0, 1]))]
    max_branch = rng.randint(*branch)
    actions = ["x", "y", "z"][:max_branch]
    depth = rng.randint(*depth)
    cond_rate = rng.choice([0.2, 0.35, 0.5])
    pos_rate = rng.choice([0.5, 0.9, 1.0])

    # Finite domains (a disjunction of values in the initial constraints) can be checked by enumerating them.
    finite = rng.random() < 0.7
    domains = {u: sorted(rng.sample(range(-1, 4), rng.randint(2, 3))) for u in unknowns} if finite else {}

    pool = None
    if rng.random() < 0.3:
        pool = {}
    copy_rate = rng.choice([0.0, 0.2])
    seen = []

    def new_leaf(names):
        nonlocal pool
        candidates = [u for k, u in seen if k <= names]
        if candidates and rng.random() < copy_rate:
            return copy.deepcopy(rng.choice(candidates))
        if pool is not None:
            # repeated terms give ties
            key = frozenset(names)
            terms = pool.setdefault(key, [gen_utility(rng, sorted(names), infinitesimals, pos_rate, None, 0.4)
                                          for _ in range(rng.randint(2, 4))])
            u = [{"player": p, "value": rng.choice(terms)} for p in players]
        else:
            u = [{"player": p, "value": gen_utility(rng, sorted(names), infinitesimals, pos_rate, None, 0.4)}
                 for p in players]
        seen.append((frozenset(names), copy.deepcopy(u)))
        return u

    def gen_tree(depth, is_root, names, revealed):
        if not is_root and (depth == 0 or rng.random() < stop_rate):
            return {"utility": new_leaf(names)}
        if rng.random() < (cond_rate if not is_root else cond_rate / 3):
            hidden = [u for u in unknowns if u not in revealed]
            if hidden and rng.random() < 0.8:
                u = rng.choice(hidden)
            else:
                u = rng.choice([u for u in unknowns if u in revealed] or [None])
            conds = gen_conditions(rng, u, domains, known)
            node = {"condition": []}
            here = set(IDENT.findall(" ".join(conds))) & set(unknowns)
            others = [v for v in hidden if v not in here]
            if others and rng.random() < 0.3:
                node["reveals"] = [rng.choice(others)]
            if TRUE_CONDITIONS and hidden and rng.random() < 0.15:
                conds, node["reveals"] = ["true"], [rng.choice(hidden)]
            here |= set(node.get("reveals", []))
            # condition nodes count towards the depth only sometimes, to keep the trees small
            below = depth - 1 if rng.random() < 0.5 else depth
            node["condition"] = [{"constraint": c, "child": gen_tree(below, False, names | here, revealed | here)}
                                 for c in conds]
            return node
        n = rng.randint(1 if not is_root else 2, max_branch)
        return {"player": rng.choice(players),
                "children": [{"action": a, "child": gen_tree(depth - 1, False, names, revealed)}
                             for a in rng.sample(actions, n)]}

    # at least one condition node, otherwise it is an EFG (or the unknowns do not matter)
    while True:
        seen.clear()
        tree = gen_tree(depth, True, set(known), frozenset())
        if any(is_condition(n) for n in nodes(tree)):
            break

    positive = ["%s > 0" % c for c in known + infinitesimals if rng.random() < 0.6]
    domain_constraints = [" | ".join("%s = %d" % (u, v) for v in vs) for u, vs in domains.items()]
    while True:
        initial = positive + domain_constraints + [gen_constraint(rng, known, infinitesimals)
                                                   for _ in range(rng.randint(0, 1))]
        if len(unknowns) > 1 and rng.random() < 0.3:
            initial.append("%s %s %s" % (unknowns[1], rng.choice(["=", ">=", "<="]), unknowns[0]))
        if unknowns and not finite and rng.random() < 0.4:
            initial.append("%s %s %s" % (rng.choice(unknowns), rng.choice([">", ">=", "<"]),
                                         lin_term(rng, known, 1, 2)))
        prop = {p: [gen_constraint(rng, known, infinitesimals) for _ in range(rng.choice([0, 0, 0, 1]))]
                for p in PROPS}
        if all(satisfiable(initial + prop[p], known + unknowns, infinitesimals) for p in PROPS):
            break

    def gen_honest(node):
        if "utility" in node:
            return []
        if is_condition(node):
            return [[{"condition": c["constraint"], "path": gen_honest(c["child"])} for c in node["condition"]]]
        # long honest histories exercise more of the honest-node logic
        children = node["children"]
        inner = [c for c in children if "utility" not in c["child"]]
        c = rng.choice(inner if inner and rng.random() < 0.6 else children)
        return [c["action"]] + gen_honest(c["child"])

    honest = []
    for _ in range(rng.choice([1, 1, 2])):
        h = gen_honest(tree)
        if h not in honest:
            honest.append(h)
    # random leaves rarely make the honest history secure; favour it sometimes so YES answers occur
    if rng.random() < 0.6:
        for h in honest:
            for _, leaf in honest_leaves(tree, h):
                for u in leaf["utility"]:
                    if not u["value"].endswith("+ 4"):
                        u["value"] = "%s + 4" % u["value"]
    game = {
        "players": players,
        "actions": actions,
        "infinitesimals": infinitesimals,
        "constants": declare(known, unknowns),
        "initial_constraints": initial,
        "property_constraints": prop,
        "honest_histories": honest,
        "honest_utilities": [],
        "tree": tree,
    }
    # sometimes no honest history, only an honest utility (as for a subtree off the honest history)
    if rng.random() < 0.15:
        game["honest_utilities"] = [{"utility": honest_utility(tree, honest[0])}]
        game["honest_histories"] = []
    return game


# ---- EFGs embedded into CEFGs ------------------------------------------------------

def wrap(node, conds, reveals=()):
    """A condition node with a copy of `node` below each condition: nothing changes."""
    w = {"condition": [{"constraint": c, "child": copy.deepcopy(node)} for c in conds]}
    if reveals:
        w["reveals"] = list(reveals)
    return w


def wrap_history(rest, conds):
    return [[{"condition": c, "path": copy.deepcopy(rest)} for c in conds]]


def embed_efg(game, rng):
    """A CEFG with the same verdicts as the EFG `game`: condition nodes with copies of the same subtree below each
    condition, deep in the tree on known constants, and at the root revealing constants that are now unknown.
    Returns (CEFG, description)."""
    g = copy.deepcopy(game)
    constants = g["constants"]
    what = []
    inner = rng.random() < 0.6
    if inner:
        positions = []

        def walk(node, steps):
            positions.append(steps)
            for step, c in edges(node):
                walk(c, steps + [step])
        walk(g["tree"], [])
        steps = rng.choice(positions[1:])
        conds = gen_conditions(rng, None, {}, constants)
        parent = node_at(g["tree"], steps[:-1])
        for c in parent["children"]:
            if c["action"] == steps[-1][1]:
                c["child"] = wrap(c["child"], conds)
        g["honest_histories"] = [h[:len(steps)] + wrap_history(h[len(steps):], conds)
                                 if [a for _, a in steps] == h[:len(steps)] else h
                                 for h in g["honest_histories"]]
        what.append("condition node on %s at %s" % (conds[0].split()[0], [a for _, a in steps]))
    if not inner or rng.random() < 0.6:
        unknown = rng.sample(constants, rng.randint(1, len(constants)))
        u = rng.choice(unknown)
        t = rng.randint(-1, 2)
        conds = ["%s >= %d" % (u, t), "%s < %d" % (u, t)]
        g["tree"] = wrap(g["tree"], conds, [v for v in unknown if v != u])
        g["honest_histories"] = [wrap_history(h, conds) for h in g["honest_histories"]]
        g["constants"] = declare([c for c in constants if c not in unknown], unknown)
        what.append("root condition node revealing unknown %s" % ", ".join(sorted(unknown)))
    return g, "; ".join(what)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--embed", action="store_true", help="embed a random EFG instead")
    ap.add_argument("-o", "--output", default=None)
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**63)
    rng = random.Random(seed)
    game = embed_efg(gen_game(rng), rng)[0] if args.embed else gen_cefg(rng)
    out = open(args.output, "w") if args.output else sys.stdout
    json.dump(game, out, indent=2)
    out.write("\n")


if __name__ == "__main__":
    main()
