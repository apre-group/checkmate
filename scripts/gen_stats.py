#!/usr/bin/env python3
# Statistics on generated games and checkmate's results, to tune gen_game.py.
# Usage (from the repo root): scripts/gen_stats.py [--num N] [-j JOBS] [--checkmate PATH]

import argparse
import collections
import json
import os
import random
import subprocess
import sys
import tempfile
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_game import gen_game

PROPS = ["weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"]


def tree_stats(tree):
    s = {"leaves": 0, "branches": 0, "depth": 0, "max_branching": 0, "utilities": collections.Counter()}

    def walk(t, d):
        if "utility" in t:
            s["leaves"] += 1
            s["depth"] = max(s["depth"], d)
            s["utilities"][tuple(u["value"] for u in t["utility"])] += 1
            return
        s["branches"] += 1
        s["max_branching"] = max(s["max_branching"], len(t["children"]))
        for c in t["children"]:
            walk(c["child"], d + 1)
    walk(tree, 0)
    return s


def one(job):
    seed, checkmate, tmp = job
    g = gen_game(random.Random(seed))
    t = tree_stats(g["tree"])
    path = os.path.join(tmp, "g%d.json" % seed)
    with open(path, "w") as f:
        json.dump(g, f)
    start = time.time()
    try:
        subprocess.run([checkmate, path, "--all_cases", "--json-out", path + ".out"],
                       capture_output=True, timeout=60)
        results = json.load(open(path + ".out"))["results"]
    except (subprocess.TimeoutExpired, OSError, ValueError):
        results = None
    return {
        "players": len(g["players"]),
        "constants": len(g["constants"]),
        "infinitesimals": len(g["infinitesimals"]),
        "inf_in_utilities": any(e in u for u in sum(t["utilities"].keys(), ()) for e in g["infinitesimals"]),
        "constraints": len(g["initial_constraints"]) + sum(len(c) for c in g["property_constraints"].values()),
        "honest": len(g["honest_histories"]),
        "honest_len": max(len(h) for h in g["honest_histories"]),
        "leaves": t["leaves"],
        "depth": t["depth"],
        "max_branching": t["max_branching"],
        "repeated_leaves": sum(n > 1 for n in t["utilities"].values()) > 0,
        "time": time.time() - start,
        "results": None if results is None else
        [(tuple(r["history"]), r["property"], r["holds"], len(r["cases"]),
          sum(not c["holds"] for c in r["cases"])) for r in results],
    }


def quantiles(xs):
    xs = sorted(xs)
    if not xs:
        return "-"
    return "median %s, p90 %s, max %s" % (xs[len(xs) // 2], xs[int(len(xs) * .9)], xs[-1])


def hist(xs):
    return ", ".join("%s: %d" % kv for kv in sorted(collections.Counter(xs).items()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--num", "-n", type=int, default=500)
    ap.add_argument("-j", type=int, default=os.cpu_count())
    ap.add_argument("--checkmate", default="build/checkmate")
    ap.add_argument("--seed", type=int, default=0, help="first seed; games use seeds seed..seed+num-1")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory() as tmp, Pool(args.j) as pool:
        stats = pool.map(one, [(args.seed + i, args.checkmate, tmp) for i in range(args.num)])
    done = [s for s in stats if s["results"] is not None]
    n = len(stats)

    print("%d games, %d timed out or failed" % (n, n - len(done)))
    print()
    print("Game shape")
    print("  players:          %s" % hist(s["players"] for s in stats))
    print("  constants:        %s" % hist(s["constants"] for s in stats))
    print("  infinitesimals:   %s; used in utilities in %d%% of games"
          % (hist(s["infinitesimals"] for s in stats), 100 * sum(s["inf_in_utilities"] for s in stats) // n))
    print("  constraints:      %s" % quantiles([s["constraints"] for s in stats]))
    print("  honest histories: %s; longest %s" % (hist(s["honest"] for s in stats),
                                                   quantiles([s["honest_len"] for s in stats])))
    print("  leaves:           %s" % quantiles([s["leaves"] for s in stats]))
    print("  depth:            %s" % quantiles([s["depth"] for s in stats]))
    print("  max branching:    %s" % hist(s["max_branching"] for s in stats))
    print("  repeated leaves:  %d%% of games" % (100 * sum(s["repeated_leaves"] for s in stats) // n))
    print("  checkmate time:   %s (seconds, --all_cases)"
          % quantiles([round(s["time"], 2) for s in done]))
    print()
    print("Results (with --all_cases)")
    per = collections.defaultdict(list)
    for s in done:
        for _, p, holds, cases, violated in s["results"]:
            per[p].append((holds, cases, violated))
    for p in PROPS:
        rs = per[p]
        if not rs:
            continue
        print("  %-21s YES %3d%%, split %3d%%, mixed (some cases hold, some not) %3d%%, cases: %s"
              % (p, 100 * sum(r[0] for r in rs) // len(rs), 100 * sum(r[1] > 1 for r in rs) // len(rs),
                 100 * sum(0 < r[2] < r[1] for r in rs) // len(rs), quantiles([r[1] for r in rs])))

    differ = 0
    for s in done:
        v = {(h, p): holds for h, p, holds, _, _ in s["results"]}
        differ += any(v[(h, "weak_immunity")] != v.get((h, "weaker_immunity")) for h, p in v if p == "weak_immunity")
    print("  weak and weaker immunity differ in %d%% of games" % (100 * differ // max(len(done), 1)))


if __name__ == "__main__":
    main()
