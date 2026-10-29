#!/usr/bin/env python3
# Fuzz checkmate with random games, EFGs and conditional games (CEFGs).
# Run from the repo root: scripts/fuzz.py [--num N] [--seed S] [--games efg|cefg|both] [--quiet]

import argparse
import collections
import json
import os
import random
import re
import shlex
import stat
import subprocess
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPTS)
from gen_game import gen_game
from gen_cefg import declared, embed_efg, gen_cefg, nodes, revealed_at
from transform import random_transform
from compose import cefg_split, cefg_splice, split, splice

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
    if STATS["efg games"]:
        print_efg_stats(line)
    if STATS["cefg games"]:
        print_cefg_stats(line)


def print_efg_stats(line):
    print("  EFGs: %d games" % STATS["efg games"])
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


COND_BUCKETS = (0, 1, 3, 6)


def note_cefg(game_json, verdicts, embedded):
    known, unknown = declared(game_json["constants"])
    tree = game_json["tree"]
    conds = [n for n in nodes(tree) if "condition" in n]
    hists = game_json["honest_histories"]
    STATS["cefg games"] += 1
    STATS["cefg embedded EFGs"] += embedded
    STATS["cefg players %d" % len(game_json["players"])] += 1
    STATS["cefg leaves " + bucket(sum("utility" in n for n in nodes(tree)), LEAF_BUCKETS)] += 1
    STATS["cefg unknowns %d" % len(unknown)] += 1
    STATS["cefg condition nodes " + bucket(len(conds), COND_BUCKETS)] += 1
    STATS["cefg with revealing condition nodes"] += any(revealed_at(n, unknown) for n in conds)
    STATS["cefg honest through conditions"] += any(not isinstance(e, str) for h in hists for e in h)
    STATS["cefg honest utility only"] += not hists
    for (_, _, p), v in verdicts.items():
        STATS["cefg %s runs" % p] += 1
        STATS["cefg %s %s" % (p, {True: "YES", False: "NO", None: "UNKNOWN"}[v])] += 1


def print_cefg_stats(line):
    print("  CEFGs: %d games, %d of them embedded EFGs" % (STATS["cefg games"], STATS["cefg embedded EFGs"]))
    print(line("players", ["cefg players %d" % n for n in range(2, 7)], "cefg players "))
    print(line("leaves", ["cefg leaves " + bucket(n, LEAF_BUCKETS) for n in (1, 4, 9, 17, 33)], "cefg leaves "))
    print(line("unknowns", ["cefg unknowns %d" % n for n in range(4)], "cefg unknowns "))
    print(line("condition nodes", ["cefg condition nodes " + bucket(n, COND_BUCKETS) for n in (0, 1, 2, 4, 7)],
               "cefg condition nodes "))
    print(line("games", ["cefg with revealing condition nodes",
                         "cefg honest through conditions", "cefg honest utility only"], "cefg "))
    for p in PROPS:
        n = STATS["cefg %s runs" % p]
        if n:
            print("  %-21s YES %3d%%, NO %3d%%, UNKNOWN %3d%% of %d runs"
                  % (p, 100 * STATS["cefg %s YES" % p] // n, 100 * STATS["cefg %s NO" % p] // n,
                     100 * STATS["cefg %s UNKNOWN" % p] // n, n))
    print(line("conditions", ["cefg rejected overlap", "cefg rejected gap", "cefg defect unreachable"], "cefg "))
    print(line("subtrees", ["cefg cut along honest", "cefg cut off honest", "cefg cut nested"], "cefg "))
    print(line("transforms", sorted(k for k in STATS if k.startswith("cefg transform ")), "cefg transform "))
    print(line("compared", ["cefg compared with EFG", "cefg compared options", "cefg compared transformed",
                            "cefg compared supertree"], "cefg compared "))


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


def repro_options():
    opts = ""
    if args.wasm:
        opts += " --wasm --wasm-dir " + shlex.quote(args.wasm_dir)
    elif args.checkmate != "build/checkmate":
        opts += " --checkmate " + shlex.quote(args.checkmate)
    if args.js_gen:
        opts += " --js-gen"
    return opts


def checkmate_cmd():
    if args.wasm:
        return ["node", os.path.join(SCRIPTS, "checkmate_wasm.js"), "--wasm-dir", args.wasm_dir]
    return [args.checkmate]


def run_checkmate(game, flags, json_out=None, allowed=None):
    """Run checkmate, return the --json-out results, or else its output; None on a timeout.
    `allowed` matches the lines starting with "checkmate:" that are expected warnings, not errors."""
    cmd = checkmate_cmd() + [game] + flags + (["--json-out", json_out] if json_out else [])
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
        if allowed and allowed.match(line):
            continue
        if "Assertion" in line or "terminate called" in line or "checkmate:" in line or "runtime error:" in line:
            raise Bug("checkmate printed an error: %s" % line, cmd, p.stdout)
    return json.load(open(json_out))["results"] if json_out else p.stdout


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
                  % fmt_cmd(checkmate_cmd() + [game] + flags + ["--json-out", json_out]), cmd, p.stdout)
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


def fuzz_efg(rng, game, outs):
    STATS["efg games"] += 1
    if args.js_gen:
        js_seed = rng.randrange(2**31)
        p = subprocess.run(["node", os.path.join(SCRIPTS, "gen_game_js.js"), str(js_seed)],
                           stdout=subprocess.PIPE, universal_newlines=True, check=True)
        game_json = json.loads(p.stdout)
        print("Generated with html/gen_game.js, seed %d" % js_seed)
    else:
        game_json = gen_game(rng)
    with open(game, "w") as f:
        json.dump(game_json, f, indent=2)
    base_out = game[:-5] + "-base.out.json"
    outs.append(base_out)
    base = run_checkmate(game, [], base_out)
    if base is None:
        return
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


# ---- conditional games (CEFGs) ----------------------------------------------------
# The verdicts of a CEFG come from --json-out (cefg_verdicts), keyed by (kind, index, property) for the index-th
# honest history ("history"), honest utility ("utility") or the run without honest history ("none"). They must
# agree with the verdicts in the text output (parse_verdicts).

# options the CEFG analysis ignores with a warning: running with them must not change anything
CEFG_IGNORED = ["--counterexamples", "--all_counterexamples", "--all_cases", "--strategies", "--preconditions"] + NO_OPTS
IGNORED_WARNING = re.compile(r"checkmate: (--[\w-]+ (is not yet implemented for CEFGs|only applies to C?EFGs) and is ignored$"
                             r"|note: condition \d+ .* can never hold"
                             r"|warning: could not check whether .*, Z3 gave up$)")

# --no_validate_conditions for the game being fuzzed if its conditions overlap or leave a gap (see check_conditions),
# so that the analysis runs anyway
CONDITION_FLAGS = []
# the errors of CheckMate's checks of the conditions, by the defect gen_cefg records
CONDITION_ERRORS = {"overlap": re.compile(r"checkmate: .*\boverlap: both hold for some values"),
                    "gap": re.compile(r"checkmate: .*(leave a gap: no condition holds|no condition of .* can hold)")}

VERDICT = re.compile(r"^(YES|NO|UNKNOWN), .*?\b(weaker immune|weak immune|collusion resilient|practical)\b")
PROPERTY = {"weak immune": "weak_immunity", "weaker immune": "weaker_immunity",
            "collusion resilient": "collusion_resilience", "practical": "practicality"}


def parse_verdicts(text):
    """The verdicts in checkmate's output (of a CEFG or an EFG, not in --subtree mode):
    {(kind, index, property): True, False or None (UNKNOWN)}, with kind "history" for the index-th honest history,
    "none" for the run without honest history and "utility" for the index-th honest utility."""
    verdicts, kind, counts = {}, None, {}
    for line in text.split("\n"):
        for prefix, k in [("Checking history ", "history"), ("Checking no honest history", "none"),
                          ("Checking honest utility ", "utility")]:
            if line.startswith(prefix):
                kind = (k, counts.get(k, 0))
                counts[k] = counts.get(k, 0) + 1
        m = VERDICT.match(line)
        if m and kind is not None:
            verdicts[kind + (PROPERTY[m.group(2)],)] = {"YES": True, "NO": False, "UNKNOWN": None}[m.group(1)]
    return verdicts


def history_shape(history):
    """An honest history without the conditions, which CheckMate writes in its own syntax."""
    return [e if isinstance(e, str) else [history_shape(c["path"]) for c in e] for e in history]


def cefg_verdicts(results, cmd):
    """The verdicts in a CEFG's --json-out results, keyed as the text output (see parse_verdicts), and the
    analysed honest histories, by the index of the honest history in the game. A history ending in a subtree node
    gets one run for each honest history inside the subtree; the fuzzer's subtrees have only one."""
    verdicts, histories = {}, {}
    for r in results:
        p, h, holds = r["property"], r["history"], r["holds"]
        if holds is None and (p != "practicality" or not r.get("undecided")):
            raise Bug("%s is undecided without a reason, or not for practicality: %s" % (p, r), cmd)
        if h is None:
            if "honest_history" in r:
                raise Bug("a run without honest history has an honest history index: %s" % r, cmd)
            key = ("utility", r["honest_utility"], p) if "honest_utility" in r else ("none", 0, p)
        else:
            i = r["honest_history"]
            if histories.setdefault(i, h) != h:
                raise Bug("two honest histories for index %d: %s and %s" % (i, histories[i], h), cmd)
            key = ("history", i, p)
        if key in verdicts:
            raise Bug("two results for %s" % (key,), cmd)
        verdicts[key] = holds
    return verdicts, [histories[i] for i in sorted(histories)]


def run_cefg(game, flags, outs, expect_cefg=True):
    """Run checkmate on a CEFG, keep its output, return its verdicts (None on a timeout), checking that the
    output and --json-out agree."""
    json_out = game[:-5] + ("-flags" if flags else "") + ".out.json"
    flags = flags + CONDITION_FLAGS
    cmd = checkmate_cmd() + [game] + flags + ["--json-out", json_out]
    out = run_checkmate(game, flags + ["--json-out", json_out], allowed=IGNORED_WARNING)
    if out is None:
        return None
    txt = json_out[:-5] + ".txt"
    outs += [txt, json_out]
    with open(txt, "w") as f:
        f.write(out)
    # a supertree whose condition nodes are all in the subtree is an EFG
    if expect_cefg and "Game type: CEFG" not in out:
        raise Bug("the game was not analysed as a CEFG", cmd, out)
    if "Game type: CEFG" not in out:
        return parse_verdicts(out), None
    verdicts, histories = cefg_verdicts(json.load(open(json_out))["results"], cmd)
    printed = parse_verdicts(out)
    if printed != verdicts:
        raise Bug("the output says %s, --json-out says %s" % (sorted(printed.items()), sorted(verdicts.items())), cmd)
    return verdicts, histories


def check_cefg_runs(run, game_json, flags, game):
    """One verdict for each property chosen with `flags`, for each run CheckMate makes, each for its honest history
    (unless the game has subtree nodes, whose honest histories continue the ones of the game)."""
    verdicts, histories = run
    hists = game_json["honest_histories"]
    if histories is not None and not any("subtree" in n for n in nodes(game_json["tree"])):
        if [history_shape(h) for h in histories] != [history_shape(h) for h in hists]:
            raise Bug("checkmate analysed the honest histories %s, expected %s" % (histories, hists),
                      checkmate_cmd() + [game] + flags)
    props = [p for p in PROPS if "--" + p in flags] or PROPS
    expected = {("history", i, p) for i in range(len(game_json["honest_histories"])) for p in props}
    if game_json.get("honest_utilities"):
        expected |= {("none", 0, p) for p in props if p != "collusion_resilience"}
        if "collusion_resilience" in props:
            expected |= {("utility", i, "collusion_resilience") for i in range(len(game_json["honest_utilities"]))}
    if set(verdicts) != expected:
        raise Bug("checkmate analysed %s, expected %s" % (sorted(verdicts), sorted(expected)),
                  checkmate_cmd() + [game] + flags)


def compare_cefg(base, other, what, props=PROPS, keys=lambda k: k, base_what="for the game"):
    """The verdicts `other` must be those of `base` (`keys` maps them to keys of `base`), unless one is UNKNOWN."""
    for k, v in other.items():
        b = base.get(keys(k))
        if k[2] in props and v is not None and b is not None and v != b:
            raise Bug("verdict for %s is %s %s, but %s %s" % (keys(k), v, what, b, base_what))


def cefg_flags(rng, game):
    flags = []
    if rng.random() < 0.6:
        flags += ["--" + p for p in rng.sample(PROPS, rng.randint(1, 3))]
    flags += [f for f in CEFG_IGNORED if rng.random() < 0.15]
    rng.shuffle(flags)
    return flags


def fmt_steps(steps):
    return "[%s]" % ", ".join(s if kind == "a" else "condition %d" % s for kind, s in steps)


def run_cefg_subtree(sub, path, outs):
    """Analyse `sub` in --subtree mode, return its results for the supertree."""
    with open(path, "w") as f:
        json.dump(sub, f, indent=2)
    json_out = path[:-5] + ".out.json"
    outs += [path, path + ".out", json_out]
    flags = ["--subtree", "--json-out", json_out] + CONDITION_FLAGS
    if run_checkmate(path, flags, allowed=IGNORED_WARNING) is None:
        return None
    result = json.load(open(path + ".out"))
    # the EFG engine writes its result (a node, not a list) with SMT-LIB 2 cases instead
    if isinstance(result, list) and json.load(open(json_out)) != {"version": 1, "subtree": result}:
        raise Bug("--json-out differs from %s.out" % path, checkmate_cmd() + [path] + flags)
    return result


def cefg_compositional(game_json, base, rng, game, outs):
    hists = game_json["honest_histories"]
    if not hists:
        return
    j = rng.randrange(len(hists))
    whole = dict(game_json, honest_histories=[hists[j]])
    cut = cefg_split(whole, rng)
    if cut is None:
        return
    sub, steps, along = cut
    STATS["cefg cut along honest" if along else "cefg cut off honest"] += 1
    log("Cutting subtree at %s%s" % (fmt_steps(steps), " (along the honest history)" if along else ""))
    if rng.random() < 0.3:
        inner = cefg_split(sub, rng)
        if inner is not None:
            STATS["cefg cut nested"] += 1
            log("Cutting nested subtree at %s inside it" % fmt_steps(inner[1]))
            res = run_cefg_subtree(inner[0], game[:-5] + "-sub2.json", outs)
            if res is None:
                return
            sub = cefg_splice(sub, inner[1], res, inner[2])
    res = run_cefg_subtree(sub, game[:-5] + "-sub.json", outs)
    if res is None:
        return
    sup_json = cefg_splice(whole, steps, res, along)
    sup = game[:-5] + "-super.json"
    outs.append(sup)
    with open(sup, "w") as f:
        json.dump(sup_json, f, indent=2)
    run = run_cefg(sup, [], outs, expect_cefg=False)
    if run is None:
        return
    check_cefg_runs(run, sup_json, [], sup)
    compare_cefg(base, run[0], "with the subtree at %s analysed separately" % fmt_steps(steps),
                 keys=lambda k: (k[0], j, k[2]))
    STATS["cefg compared supertree"] += 1


def check_conditions(game, defects, outs):
    """CheckMate (without --no_validate_conditions) must reject a game whose conditions overlap or leave a gap, unless
    the constraints and the conditions on the way make that defect unreachable; other games must pass the checks."""
    if not defects:
        # the analysis runs without --no_validate_conditions, where run_checkmate rejects any condition error
        return
    cmd = checkmate_cmd() + [game, "--weak_immunity"]
    p = run(cmd, args.tout)
    if p is None:
        STATS["checkmate timeouts"] += 1
        return
    txt = game[:-5] + "-conditions.txt"
    outs.append(txt)
    with open(txt, "w") as f:
        f.write(p.stdout)
    if p.returncode == 0:
        STATS["cefg defect unreachable"] += 1
        return
    errors = [l for l in p.stdout.split("\n") if l.startswith("checkmate:") and not IGNORED_WARNING.match(l)]
    if p.returncode != 1 or len(errors) != 1 or not any(CONDITION_ERRORS[d].match(errors[0]) for d in defects):
        raise Bug("expected an error about the %s of the conditions" % " or ".join(sorted(set(defects))), cmd, p.stdout)
    STATS["cefg rejected " + next(d for d in sorted(set(defects)) if CONDITION_ERRORS[d].match(errors[0]))] += 1


def fuzz_cefg(rng, game, outs):
    efg_verdicts = None
    defects = []
    if rng.random() < 0.3:
        # an EFG embedded into a CEFG: the CEFG analysis must agree with the (checked) EFG analysis
        efg_json = gen_game(rng)
        efg = game[:-5] + "-efg.json"
        efg_out = game[:-5] + "-efg.out.json"
        outs += [efg, efg_out]
        with open(efg, "w") as f:
            json.dump(efg_json, f, indent=2)
        results = run_checkmate(efg, [], efg_out)
        if results is None:
            return
        check_consistent(results, [])
        run_checker(efg, efg_out, [])
        game_json, how = embed_efg(efg_json, rng)
        log("Embedded the EFG %s into a CEFG: %s" % (efg, how))
        hists = efg_json["honest_histories"]
        efg_verdicts = {("history", hists.index(r["history"]), r["property"]): r["holds"] for r in results}
    else:
        game_json = gen_cefg(rng, defects)
    with open(game, "w") as f:
        json.dump(game_json, f, indent=2)
    if defects:
        log("Conditions with defects: " + ", ".join(sorted(set(defects))))
    check_conditions(game, defects, outs)
    CONDITION_FLAGS[:] = ["--no_validate_conditions"] if defects else []

    run = run_cefg(game, [], outs)
    if run is None:
        return
    check_cefg_runs(run, game_json, [], game)
    base = run[0]
    note_cefg(game_json, base, efg_verdicts is not None)
    if efg_verdicts is not None:
        compare_cefg(efg_verdicts, base, "for the CEFG", base_what="for the EFG embedded into it")
        STATS["cefg compared with EFG"] += 1

    flags = cefg_flags(rng, game)
    run = run_cefg(game, flags, outs)
    if run is not None:
        check_cefg_runs(run, game_json, flags, game)
        compare_cefg(base, run[0], "with %s" % fmt_cmd(flags))
        STATS["cefg compared options"] += 1

    meta_json, names, _, props = random_transform(game_json, rng)
    meta = game[:-5] + "-meta.json"
    outs.append(meta)
    with open(meta, "w") as f:
        json.dump(meta_json, f, indent=2)
    log("Transforms: " + " + ".join(names))
    for t in names:
        STATS["cefg transform " + t] += 1
    run = run_cefg(meta, [], outs)
    if run is not None:
        check_cefg_runs(run, meta_json, [], meta)
        compare_cefg(base, run[0], "after transforms %s" % " + ".join(names), props)
        STATS["cefg compared transformed"] += 1

    cefg_compositional(game_json, base, rng, game, outs)


def game_kind(seed):
    """EFG or CEFG, decided by the seed alone, so that --seed reproduces it (and the game, from the same seed)."""
    if args.games != "both":
        return args.games
    return "cefg" if random.Random("games %d" % seed).random() < 0.5 else "efg"


def fuzz_one(seed):
    rng = random.Random(seed)
    LOG.clear()
    kind = game_kind(seed)
    game = unique_file("fuzzTest")
    print(col("Seed: ", MAGENTA) + str(seed) + col("  file: ", MAGENTA) + game + col("  game: ", MAGENTA) + kind.upper())
    outs = []
    try:
        (fuzz_cefg if kind == "cefg" else fuzz_efg)(rng, game, outs)
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
        print("REPRODUCE with: scripts/fuzz.py --seed %d --num 1 --games %s%s" % (seed, kind, repro_options()))
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
    ap.add_argument("--wasm", action="store_true",
                    help="run the WebAssembly build through scripts/checkmate_wasm.js instead of --checkmate")
    ap.add_argument("--wasm-dir", default=os.path.normpath(os.path.join(SCRIPTS, "..", "html")),
                    help="directory with checkmate.js and checkmate.wasm, default: html/")
    ap.add_argument("--games", choices=["efg", "cefg", "both"], default="both",
                    help="which games to fuzz: EFGs, conditional games (CEFGs) or both (default)")
    ap.add_argument("--js-gen", action="store_true",
                    help="generate EFGs with the web page's html/gen_game.js")
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
