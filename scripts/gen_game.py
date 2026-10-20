#!/usr/bin/env python3
# Random game generator for fuzzing. Usage: gen_game.py [--seed S] [-o out.json]

import argparse
import copy
import json
import random
import sys

import z3


def lin_term(rng, names, max_coef, constant_range, nonneg=False):
    parts = []
    c = rng.randint(0 if nonneg else -constant_range, constant_range)
    if c != 0 or rng.random() < 0.3:
        parts.append(str(c))
    for n in names:
        if rng.random() < 0.5:
            continue
        k = rng.randint(0 if nonneg else -max_coef, max_coef)
        if k == 0:
            continue
        parts.append(n if k == 1 else "-" + n if k == -1 else "%d*%s" % (k, n))
    if not parts:
        return "0"
    s = parts[0]
    for p in parts[1:]:
        s += " - " + p[1:] if p.startswith("-") else " + " + p
    return s


def gen_utility(rng, constants, infinitesimals, pos_rate):
    nonneg = rng.random() < pos_rate
    s = lin_term(rng, constants, 2, 3, nonneg)
    if infinitesimals and rng.random() < 0.4:
        inf = lin_term(rng, infinitesimals, 2, 0, nonneg)
        if inf != "0":
            s = "%s + (%s)" % (s, inf)
    return s


def gen_constraint(rng, constants, infinitesimals):
    if infinitesimals and rng.random() < 0.15:
        return "%s %s 0" % (rng.choice(infinitesimals), rng.choice([">", ">="]))
    op = rng.choice(["<", "<=", ">", ">=", "=", "!="])
    atom = "%s %s %s" % (lin_term(rng, constants, 2, 2), op, lin_term(rng, constants, 2, 2))
    if rng.random() < 0.1:
        atom += " | %s %s 0" % (rng.choice(constants), rng.choice(["<", ">"]))
    return atom


def gen_tree(rng, players, actions, new_leaf, depth, max_branch, is_root):
    if not is_root and (depth == 0 or rng.random() < 0.3):
        return {"utility": new_leaf()}
    n = rng.randint(1 if not is_root else 2, max_branch)
    return {
        "player": rng.choice(players),
        "children": [{"action": a,
                      "child": gen_tree(rng, players, actions, new_leaf, depth - 1, max_branch, False)}
                     for a in rng.sample(actions, n)],
    }


def leaf_histories(tree, prefix=()):
    if "utility" in tree:
        yield list(prefix)
        return
    for c in tree["children"]:
        yield from leaf_histories(c["child"], prefix + (c["action"],))


def to_z3(expr, env):
    # The input grammar is a subset of Python's once `=`, `!=`, `|` are mapped.
    expr = expr.replace("!=", "#").replace("<=", "LE").replace(">=", "GE")
    expr = expr.replace("=", "==").replace("#", "!=").replace("LE", "<=").replace("GE", ">=")
    parts = [p.strip() for p in expr.split("|")]
    return z3.Or([eval(p, {}, env) for p in parts])


def satisfiable(constraints, constants, infinitesimals):
    # Infinitesimals only meet other infinitesimals in generated constraints, so plain reals suffice.
    env = {n: z3.Real(n) for n in constants + infinitesimals}
    s = z3.Solver()
    s.set("timeout", 2000)
    for c in constraints:
        s.add(to_z3(c, env))
    return s.check() == z3.sat


def gen_game(rng):
    players = ["A", "B", "C", "D"][:rng.randint(2, 4)]
    constants = ["c%d" % i for i in range(rng.randint(1, 3))]
    infinitesimals = ["e%d" % i for i in range(rng.choice([0, 0, 1, 2]))]
    max_branch = rng.randint(2, 3)
    actions = ["x", "y", "z"][:max_branch]
    depth = rng.randint(1, 4)
    # Fully random utilities make nearly every honest history insecure, so most games lean non-negative.
    pos_rate = rng.choice([0.0, 0.5, 0.9, 1.0])
    term = lambda: gen_utility(rng, constants, infinitesimals, pos_rate)
    # Repeated terms and whole repeated leaves give ties and exercise the caches keyed by utilities.
    if rng.random() < 0.4:
        pool = [term() for _ in range(rng.randint(2, 5))]
        term = lambda: rng.choice(pool)
    copy_rate = rng.choice([0.0, 0.0, 0.2, 0.5])
    seen = []

    def new_leaf():
        if seen and rng.random() < copy_rate:
            return copy.deepcopy(rng.choice(seen))
        u = [{"player": p, "value": term()} for p in players]
        seen.append(copy.deepcopy(u))
        return u

    tree = gen_tree(rng, players, actions, new_leaf, depth, max_branch, True)

    props = ["weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"]
    positive = ["%s > 0" % c for c in constants + infinitesimals if pos_rate > 0 or rng.random() < 0.5]
    while True:
        initial = positive + [gen_constraint(rng, constants, infinitesimals)
                              for _ in range(rng.randint(0, 2))]
        prop = {p: [gen_constraint(rng, constants, infinitesimals)
                    for _ in range(rng.choice([0, 0, 0, 1]))] for p in props}
        if all(satisfiable(initial + prop[p], constants, infinitesimals) for p in props):
            break

    hists = list(leaf_histories(tree))
    honest = rng.sample(hists, min(len(hists), rng.choice([1, 1, 2])))
    # Random leaves rarely make the honest history secure; favour it sometimes so YES answers occur.
    if rng.random() < 0.6:
        for h in honest:
            node = tree
            for a in h:
                node = next(c["child"] for c in node["children"] if c["action"] == a)
            for u in node["utility"]:
                if not u["value"].endswith("+ 4"):
                    u["value"] = "%s + 4" % u["value"]
    return {
        "players": players,
        "actions": actions,
        "infinitesimals": infinitesimals,
        "constants": constants,
        "initial_constraints": initial,
        "property_constraints": prop,
        "honest_histories": honest,
        "tree": tree,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("-o", "--output", default=None)
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**63)
    game = gen_game(random.Random(seed))
    out = open(args.output, "w") if args.output else sys.stdout
    json.dump(game, out, indent=2)
    out.write("\n")


if __name__ == "__main__":
    main()
