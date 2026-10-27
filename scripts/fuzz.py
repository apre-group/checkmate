#!/usr/bin/env python3
# Fuzz checkmate with random games. Run from the repo root: scripts/fuzz.py [--num N] [--seed S] [--quiet]

import argparse
import collections
import json
import os
import random
import shlex
import stat
import subprocess
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPTS)
from gen_game import gen_game
from transform import random_transform
from compose import split, splice

_USE_COLOR = os.isatty(1) and os.environ.get("NO_COLOR") is None
GREEN, RED, BLUE, MAGENTA, CYAN = "32", "31;1", "34;1", "35", "36"

PROPS = ["weak_immunity", "weaker_immunity", "collusion_resilience", "practicality"]
NO_OPTS = ["--no-cr-node-cache", "--no-cr-leaf-cache", "--no-cr-implied-groups",
           "--no-cr-violated-lookup", "--no-problematic-groups", "--exact-splits", "--reset-from-root"]


# what the fuzzer exercised so far, printed every few iterations to see whether it covers enough
STATS = collections.Counter()


def bucket(n, limits):
    lo = 0
    for hi in limits:
        if n <= hi:
            return "%d" % n if lo + 1 == hi or lo == hi else "%d-%d" % (lo + 1, hi)
        lo = hi
    return "%d+" % (lo + 1)


LEAF_BUCKETS = (3, 8, 16, 32)


def note_game(game_json, base):
    leaves, depth, utilities = 0, 0, collections.Counter()

    def walk(t, d):
        nonlocal leaves, depth
        if "utility" in t:
            leaves += 1
            depth = max(depth, d)
            utilities[tuple(u["value"] for u in t["utility"])] += 1
        for c in t.get("children", []):
            walk(c["child"], d + 1)
    walk(game_json["tree"], 0)
    STATS["players %d" % len(game_json["players"])] += 1
    STATS["leaves " + bucket(leaves, LEAF_BUCKETS)] += 1
    STATS["depth %d" % depth] += 1
    STATS["honest length %d" % max(len(h) for h in game_json["honest_histories"])] += 1
    STATS["with infinitesimals in utilities"] += any(e in v for u in utilities for v in u for e in game_json["infinitesimals"])
    STATS["with repeated leaves"] += any(n > 1 for n in utilities.values())
    verdicts = {}
    for r in base:
        p = r["property"]
        violated = sum(not c["holds"] for c in r["cases"])
        STATS[p + " runs"] += 1
        STATS[p + " YES"] += r["holds"]
        STATS[p + " split"] += len(r["cases"]) > 1
        STATS[p + " mixed"] += 0 < violated < len(r["cases"])
        STATS[p + " max cases"] = max(STATS[p + " max cases"], len(r["cases"]))
        verdicts[(tuple(r["history"]), p)] = r["holds"]
    STATS["weak != weaker"] += any(v != verdicts.get((h, "weaker_immunity"))
                                   for (h, p), v in verdicts.items() if p == "weak_immunity")


def print_stats(iterations):
    def line(prefix, keys, strip=""):
        return "  " + prefix + ": " + (", ".join("%s %d" % (k[len(strip):], STATS[k]) for k in keys if STATS[k]) or "none")
    print(col("=== Statistics after %d iterations ===" % iterations, CYAN))
    print(line("players", ["players %d" % n for n in range(2, 7)], "players "))
    print(line("leaves", ["leaves " + bucket(n, LEAF_BUCKETS) for n in (1, 4, 9, 17, 33)], "leaves "))
    print(line("depth", ["depth %d" % n for n in range(1, 7)], "depth "))
    print(line("honest history length", ["honest length %d" % n for n in range(1, 7)], "honest length "))
    print(line("games", ["with infinitesimals in utilities", "with repeated leaves", "weak != weaker"]))
    for p in PROPS:
        n = STATS[p + " runs"]
        if n:
            print("  %-21s YES %3d%%, split %3d%%, mixed %3d%% of %d runs, most cases %d"
                  % (p, 100 * STATS[p + " YES"] // n, 100 * STATS[p + " split"] // n,
                     100 * STATS[p + " mixed"] // n, n, STATS[p + " max cases"]))
    print(line("subtrees", ["cut along honest", "cut off honest", "cut nested"]))
    print(line("transforms", sorted(k for k in STATS if k.startswith("transform ")), "transform "))
    print(line("switches", sorted(k for k in STATS if k.startswith("--no-") or k in ("--exact-splits", "--reset-from-root"))))
    print(line("verified", ["verified game", "verified transformed", "verified subtree", "verified supertree",
                            "verified strategies", "verified counterexamples", "verified preconditions"], "verified "))
    print(line("skipped", ["checker unsupported", "checker undecided", "checker timeouts", "checkmate timeouts"]))


def col(txt, code):
    return "\033[%sm%s\033[0m" % (code, txt) if _USE_COLOR else txt


# with --quiet, the details of an iteration are held back and printed only if it finds a bug
LOG = []


def log(msg):
    if args.quiet:
        LOG.append(msg)
    else:
        print(msg)


def unique_file(fname_begin, fname_end=".json", max_num_files=2700):
    counter = 1
    while True:
        fname = "out/" + fname_begin + "_" + str(counter) + fname_end
        try:
            fd = os.open(fname, os.O_CREAT | os.O_EXCL, stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return fname
        except OSError:
            pass
        counter += 1
        if counter > max_num_files:
            print("Cannot create unique_file, last try was: %s" % fname)
            sys.exit(-1)


class Bug(Exception):
    def __init__(self, what, cmd=None, output=None):
        super().__init__(what)
        self.what, self.cmd, self.output = what, cmd, output


def fmt_cmd(cmd):
    return " ".join(shlex.quote(c) for c in cmd)


def tail(out, n=60):
    lines = out.rstrip("\n").split("\n")
    return "\n".join((["[... %d lines cut ...]" % (len(lines) - n)] if len(lines) > n else []) + lines[-n:])


# For a -DSANITIZE=ON build; harmless otherwise. The link order check trips over /etc/ld.so.preload.
SANITIZER_ENV = {
    "ASAN_OPTIONS": "verify_asan_link_order=0",
    "LSAN_OPTIONS": "suppressions=" + os.path.join(SCRIPTS, "lsan.supp"),
    "UBSAN_OPTIONS": "print_stacktrace=1:halt_on_error=1",
}


def run(cmd, tout):
    log(col("--> Executing: ", BLUE) + fmt_cmd(cmd))
    try:
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              universal_newlines=True, timeout=tout, env=dict(os.environ, **SANITIZER_ENV))
    except subprocess.TimeoutExpired:
        print("Timeout after %d s, skipping" % tout)
        return None


def run_checkmate(game, flags, json_out=None):
    cmd = [args.checkmate, game] + flags + (["--json-out", json_out] if json_out else [])
    for f in flags:
        if f in NO_OPTS:
            STATS[f] += 1
    p = run(cmd, args.tout)
    if p is None:
        STATS["checkmate timeouts"] += 1
        return None
    if p.returncode != 0:
        how = "killed by signal %d" % -p.returncode if p.returncode < 0 else "exit code %d" % p.returncode
        raise Bug("checkmate crashed (%s)" % how, cmd, p.stdout)
    for line in p.stdout.split("\n"):
        if "Assertion" in line or "terminate called" in line or "checkmate:" in line or "runtime error:" in line:
            raise Bug("checkmate printed an error: %s" % line, cmd, p.stdout)
    return json.load(open(json_out))["results"] if json_out else True


def run_subtree(sub, path, rng, outs):
    """Analyse `sub` in --subtree mode, return its result node for the supertree."""
    with open(path, "w") as f:
        json.dump(sub, f, indent=2)
    json_out = path[:-5] + ".out.json"
    outs += [path, path + ".out", json_out]
    flags = ["--subtree"] + random_opts(rng)
    if run_checkmate(path, flags + ["--json-out", json_out]) is None:
        return None
    run_checker(path, json_out, flags)
    return json.load(open(path + ".out"))


def compositional(game_json, base, rng, game, outs):
    h = rng.choice(game_json["honest_histories"])
    whole = dict(game_json, honest_histories=[h])
    cut = split(whole, rng)
    if cut is None:
        return
    sub, hist = cut
    STATS["cut along honest" if sub["honest_histories"] else "cut off honest"] += 1
    log("Cutting subtree at %s%s" % (list(hist), " (along the honest history)" if sub["honest_histories"] else ""))
    if rng.random() < 0.3:
        inner = split(sub, rng)
        if inner is not None:
            STATS["cut nested"] += 1
            log("Cutting nested subtree at %s inside it" % list(inner[1]))
            res = run_subtree(inner[0], game[:-5] + "-sub2.json", rng, outs)
            if res is None:
                return
            sub = splice(sub, inner[1], res)
    res = run_subtree(sub, game[:-5] + "-sub.json", rng, outs)
    if res is None:
        return
    sup = game[:-5] + "-super.json"
    outs.append(sup)
    with open(sup, "w") as f:
        json.dump(splice(whole, hist, res), f, indent=2)
    flags = random_flags(rng)
    out = game[:-5] + "-super.out.json"
    outs.append(out)
    results = run_checkmate(sup, flags, out)
    if results is not None:
        check_consistent(results, flags)
        compare_verdicts(base, results, "the subtree at %s analysed separately, %s" % (list(hist), fmt_cmd(flags)))
        run_checker(sup, out, flags)


def run_checker(game, json_out, flags):
    cmd = [sys.executable, os.path.join(SCRIPTS, "check_result.py"), game, json_out]
    if "--all_cases" in flags:
        cmd.append("--complete-cases")
    if "--subtree" in flags:
        cmd.append("--subtree")
    p = run(cmd, args.check_tout)
    if p is None:
        STATS["checker timeouts"] += 1
        return
    if p.returncode == 2:
        STATS["checker undecided"] += 1
        print("Checker could not decide, skipping:")
        print(tail(p.stdout, 10))
        return
    if p.returncode != 0:
        raise Bug("verification of checkmate's results failed. checkmate ran as:\n  %s"
                  % fmt_cmd([args.checkmate, game] + flags + ["--json-out", json_out]), cmd, p.stdout)
    if p.stdout.startswith("UNSUPPORTED"):
        STATS["checker unsupported"] += 1
        print(p.stdout.strip())
        return
    kind = ("subtree" if "--subtree" in flags else "supertree" if game.endswith("-super.json")
            else "transformed" if game.endswith("-meta.json") else "game")
    STATS["verified " + kind] += 1
    if kind != "subtree":
        for r in json.load(open(json_out))["results"]:
            STATS["verified strategies"] += len(r["strategies"])
            STATS["verified counterexamples"] += len(r["counterexamples"])
            STATS["verified preconditions"] += "precondition" in r
    log(p.stdout.strip().split("\n")[-1])


def key(r):
    return (tuple(r["history"]) if r["history"] is not None else None,
            r.get("honest_utility"), r["property"])


def check_consistent(results, flags):
    for r in results:
        if not r["cases"]:
            raise Bug("no cases recorded for %s" % (key(r),))
        if r["holds"] != all(c["holds"] for c in r["cases"]):
            raise Bug("verdict %s disagrees with its cases for %s" % (r["holds"], key(r)))
        if "--all_cases" not in flags and "--preconditions" not in flags:
            if sum(not c["holds"] for c in r["cases"]) > 1:
                raise Bug("more than one violated case without --all_cases for %s" % (key(r),))


def compare_verdicts(base, other, flags):
    base_v = {key(r): r["holds"] for r in base}
    for r in other:
        if base_v.get(key(r)) != r["holds"]:
            raise Bug("verdict for %s is %s with %s, but %s without"
                      % (key(r), r["holds"], flags, base_v.get(key(r))))


def compare_transformed(base, other, names, action_map, props):
    base_v = {key(r): r["holds"] for r in base if r["property"] in props}
    inverse = {b: a for a, b in action_map.items()}
    for r in other:
        if r["property"] not in props:
            continue
        h = r["history"]
        k = (tuple(inverse.get(a, a) for a in h) if h is not None else None,
             r.get("honest_utility"), r["property"])
        if base_v.get(k) != r["holds"]:
            raise Bug("verdict for %s is %s after transforms %s, but %s before"
                      % (k, r["holds"], " + ".join(names), base_v.get(k)))


def random_opts(rng):
    return [o for o in NO_OPTS if rng.random() < 0.3]


def random_flags(rng):
    flags = random_opts(rng)
    if rng.random() < 0.5:
        flags += ["--" + p for p in rng.sample(PROPS, rng.randint(1, 3))]
    for f in ["--counterexamples", "--all_counterexamples", "--all_cases", "--strategies", "--preconditions"]:
        if rng.random() < 0.4:
            flags.append(f)
    rng.shuffle(flags)
    return flags


def fuzz_one(seed):
    rng = random.Random(seed)
    LOG.clear()
    game = unique_file("fuzzTest")
    print(col("Seed: ", MAGENTA) + str(seed) + col("  file: ", MAGENTA) + game)
    game_json = gen_game(rng)
    with open(game, "w") as f:
        json.dump(game_json, f, indent=2)
    outs = []
    try:
        base_out = game[:-5] + "-base.out.json"
        outs.append(base_out)
        base = run_checkmate(game, [], base_out)
        if base is None:
            return True
        check_consistent(base, [])
        note_game(game_json, base)
        run_checker(game, base_out, [])

        cert_flags = (["--strategies", "--counterexamples"] + (["--all_cases"] if rng.random() < 0.5 else [])
                      + random_opts(rng))
        for name, flags in [("cert", cert_flags), ("flags", random_flags(rng))]:
            out = "%s-%s.out.json" % (game[:-5], name)
            outs.append(out)
            other = run_checkmate(game, flags, out)
            if other is None:
                continue
            check_consistent(other, flags)
            compare_verdicts(base, other, flags)
            run_checker(game, out, flags)

        meta_json, names, action_map, props = random_transform(game_json, rng)
        meta = game[:-5] + "-meta.json"
        outs.append(meta)
        with open(meta, "w") as f:
            json.dump(meta_json, f, indent=2)
        log("Transforms: " + " + ".join(names))
        for t in names:
            STATS["transform " + t] += 1
        flags = random_opts(rng)
        out = game[:-5] + "-meta.out.json"
        outs.append(out)
        other = run_checkmate(meta, flags, out)
        if other is not None:
            check_consistent(other, flags)
            compare_transformed(base, other, names, action_map, props)
            run_checker(meta, out, flags)

        compositional(game_json, base, rng, game, outs)
    except Bug as e:
        for line in LOG:
            print(line)
        print(col("=" * 60, RED))
        print(col("BUG: ", RED) + e.what)
        if e.cmd:
            print("Command was: %s" % fmt_cmd(e.cmd))
        if e.output:
            full = game[:-5] + "-failure.txt"
            with open(full, "w") as f:
                f.write(e.output)
            outs.append(full)
            print("Output was (all of it in %s):" % full)
            print(tail(e.output))
        print("Game kept in %s, other files: %s" % (game, " ".join(outs)))
        print("REPRODUCE with: scripts/fuzz.py --seed %d --num 1" % seed)
        print(col("=" * 60, RED))
        return False
    for f in [game] + outs:
        if os.path.exists(f):
            os.unlink(f)
    print(col("OK", GREEN))
    return True


def main():
    global args
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=None, help="seed of a single iteration")
    ap.add_argument("--num", "-n", type=int, default=None, help="iterations, default: unlimited")
    ap.add_argument("--tout", "-t", type=int, default=20, help="timeout per checkmate call")
    ap.add_argument("--check-tout", type=int, default=20,
                    help="timeout per check_result.py call")
    ap.add_argument("--checkmate", default="build/checkmate")
    ap.add_argument("--stats-every", type=int, default=10, help="print statistics every N iterations")
    ap.add_argument("--quiet", "-q", action="store_true",
                    help="print only seeds, statistics and bugs (with the details of the failing iteration)")
    args = ap.parse_args()
    os.makedirs("out", exist_ok=True)

    i = 0
    while args.num is None or i < args.num:
        i += 1
        seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**63)
        if not fuzz_one(seed):
            print_stats(i)
            sys.exit(1)
        if i % args.stats_every == 0:
            print_stats(i)
    if i % args.stats_every:
        print_stats(i)
    print(col("Done: %d iterations, no bugs" % i, GREEN))


if __name__ == "__main__":
    main()
