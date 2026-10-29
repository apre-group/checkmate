#!/usr/bin/env python3
# Fuzz the compact format: JSON -> compact -> JSON -> compact must be stable and analyse the same,
# for EFGs and CEFGs (games with condition nodes).
# Run from the repo root: scripts/fuzz_compact.py [--num N] [--seed S] [--js-gen]

import argparse
import copy
import json
import os
import random
import shlex
import subprocess
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPTS)
from compose import split, splice
from fuzz import unique_file
from gen_cefg import embed_efg, gen_cefg
from gen_game import gen_game

PROPS = ["weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"]


class Bug(Exception):
    pass


def run(cmd, check_rc=True):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, universal_newlines=True, timeout=args.tout)
    if p.returncode < 0 or (check_rc and p.returncode != 0):
        raise Bug("%s failed with %d:\n%s\ncommand: %s" % (cmd[0], p.returncode, p.stdout[-2000:],
                                                       " ".join(shlex.quote(c) for c in cmd)))
    return p


def convert(path, out):
    run([args.convert, path, out])
    return open(out).read()


def is_condition(node):
    return isinstance(node.get("condition"), list)


def normalize(game):
    """The game as checkmate sees it: actions are derived from the tree, empty lists may be missing,
    and constants without unknown ones are a list."""
    g = copy.deepcopy(game)
    g.pop("actions", None)
    g["property_constraints"] = {p: g.get("property_constraints", {}).get(p, []) for p in PROPS}
    if not g.get("honest_utilities"):
        g.pop("honest_utilities", None)
    for k in ("constants", "infinitesimals"):
        d = g.get(k, [])
        if isinstance(d, dict):
            d = {"known": d.get("known", []), "unknown": d["unknown"]} if d.get("unknown") else d.get("known", [])
        g[k] = d
    g.setdefault("initial_constraints", [])

    def utilities(us):
        for u in us:
            if "condition" in u:
                utilities(u["utility"])
            else:
                u["value"] = str(u["value"])

    def walk(t):
        utilities(t.get("utility", []))
        for c in t.get("children", []):
            walk(c["child"])
        if is_condition(t):
            if not t.get("reveals", True):
                del t["reveals"]
            for c in t["condition"]:
                walk(c["child"])
        else:
            t.pop("condition", None)  # "True", written on every node by older versions of examples/dsl.py
    walk(g["tree"])
    for u in g.get("honest_utilities", []):
        utilities(u["utility"])
    return g


def tree_actions(tree):
    seen = []

    def walk(t):
        for c in t.get("children", []):
            if c["action"] not in seen:
                seen.append(c["action"])
            walk(c["child"])
        if is_condition(t):
            for c in t["condition"]:
                walk(c["child"])
    walk(tree)
    return seen


def make_game(rng, base):
    if args.js_gen:
        p = run(["node", os.path.join(SCRIPTS, "gen_game_js.js"), str(rng.randrange(2**31))])
        game = json.loads(p.stdout)
    else:
        game = gen_game(rng)
    kind = rng.choice(["plain", "plain", "subtree", "supertree", "cefg", "cefg", "embedded"])
    if kind == "plain":
        return game, kind
    if kind == "cefg":
        return gen_cefg(rng), kind
    if kind == "embedded":
        return embed_efg(game, rng)[0], "cefg (embedded EFG)"
    whole = dict(game, honest_histories=[rng.choice(game["honest_histories"])])
    cut = split(whole, rng)
    if cut is None:
        return game, "plain"
    sub, hist = cut
    if kind == "subtree":
        return sub, "subtree" + ("" if sub["honest_histories"] else " (off the honest history)")
    path = base + "-sub.json"
    with open(path, "w") as f:
        json.dump(sub, f)
    run([args.checkmate, path, "--subtree"])
    return splice(whole, hist, json.load(open(path + ".out"))), "supertree"


def mutate(rng, text):
    lines = text.split("\n")
    for _ in range(rng.randint(1, 3)):
        i = rng.randrange(len(lines))
        op = rng.choice(["delete line", "duplicate line", "cut line", "delete char", "insert char"])
        if op == "delete line":
            del lines[i]
        elif op == "duplicate line":
            lines.insert(i, lines[i])
        elif op == "cut line":
            lines[i] = lines[i][:rng.randrange(len(lines[i]) + 1)]
        elif lines[i]:
            j = rng.randrange(len(lines[i]))
            ch = rng.choice(" :,;>-#{}()?abAxu0\t") if op == "insert char" else ""
            lines[i] = lines[i][:j] + ch + lines[i][j + (op == "delete char"):]
        if not lines:
            lines = [""]
    return "\n".join(lines)


def fuzz_one(seed, stats):
    rng = random.Random(seed)
    base = unique_file("compactTest", "")
    files = [base]
    try:
        game, kind = make_game(rng, base)
        files += [base + "-sub.json", base + "-sub.json.out"]
        stats[kind] = stats.get(kind, 0) + 1
        j0, c1, j1, c2 = (base + s for s in (".json", ".game", "-back.json", "-again.game"))
        files += [j0, c1, j1, c2]
        with open(j0, "w") as f:
            json.dump(game, f, indent=2)
        text1 = convert(j0, c1)
        back = json.loads(convert(c1, j1))
        text2 = convert(j1, c2)
        if text1 != text2:
            raise Bug("compact text changed in the second round trip: compare %s and %s" % (c1, c2))
        if normalize(back) != normalize(game):
            raise Bug("JSON changed in the round trip: compare %s and %s" % (j0, j1))
        if back["actions"] != tree_actions(game["tree"]):
            raise Bug("derived actions %s, but the tree uses %s" % (back["actions"], tree_actions(game["tree"])))

        r0, r1 = base + "-json.out.json", base + "-compact.out.json"
        files += [r0, r1]
        # (CEFGs ignore these options)
        flags = [] if kind.startswith("cefg") else \
            rng.choice([[], ["--strategies", "--counterexamples"], ["--all_cases", "--preconditions"]])
        try:
            a = run([args.checkmate, j0] + flags + ["--json-out", r0], check_rc=False)
            b = run([args.checkmate, c1] + flags + ["--json-out", r1], check_rc=False)
        except subprocess.TimeoutExpired:
            a = b = None
            stats["analysis timeouts"] = stats.get("analysis timeouts", 0) + 1
        if a is None:
            pass
        elif a.returncode != b.returncode:
            raise Bug("checkmate exits with %d on the JSON but %d on the compact file" % (a.returncode, b.returncode))
        elif a.returncode == 0 and json.load(open(r0)) != json.load(open(r1)):
            raise Bug("checkmate results differ between %s and %s (%s)" % (j0, c1, " ".join(flags)))
        stats["analysed"] = stats.get("analysed", 0) + (a is not None and a.returncode == 0)

        for k in range(5):
            m = base + "-mutated%d.game" % k
            files.append(m)
            with open(m, "w") as f:
                f.write(mutate(rng, text1))
            p = run([args.convert, m], check_rc=False)
            if p.returncode not in (0, 1):
                raise Bug("checkmate-convert crashed (%d) on the mutated %s:\n%s" % (p.returncode, m, p.stdout[-2000:]))
            stats["mutants rejected" if p.returncode else "mutants accepted"] = \
                stats.get("mutants rejected" if p.returncode else "mutants accepted", 0) + 1
    except Bug as e:
        print("=" * 60)
        print("BUG: %s" % e)
        print("REPRODUCE with: scripts/fuzz_compact.py --seed %d --num 1%s" % (seed, " --js-gen" if args.js_gen else ""))
        print("=" * 60)
        return False
    for f in files:
        if os.path.exists(f):
            os.unlink(f)
    return True


def main():
    global args
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=None, help="seed of a single iteration")
    ap.add_argument("--num", "-n", type=int, default=None, help="iterations, default: unlimited")
    ap.add_argument("--tout", "-t", type=int, default=20)
    ap.add_argument("--checkmate", default="build/checkmate")
    ap.add_argument("--convert", default="build/checkmate-convert")
    ap.add_argument("--js-gen", action="store_true", help="generate games with the web page's html/gen_game.js")
    args = ap.parse_args()
    os.makedirs("out", exist_ok=True)
    stats = {}
    i = 0
    while args.num is None or i < args.num:
        i += 1
        seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**63)
        ok = fuzz_one(seed, stats)
        if not ok or i % 50 == 0 or i == args.num:
            print("after %d iterations: %s" % (i, ", ".join("%s %d" % kv for kv in sorted(stats.items()))))
        if not ok:
            sys.exit(1)
    print("Done: %d iterations, no bugs" % i)


if __name__ == "__main__":
    main()
