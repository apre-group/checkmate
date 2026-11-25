#!/usr/bin/env python3
# Shrink a game (JSON) while checkmate's output still contains a text, e.g. an error a fuzzer found. The smallest
# game so far is written to OUTPUT after every step, so stopping it at any time leaves a smaller game there.
# Usage: scripts/reduce_game.py GAME.json OUTPUT.json --grep TEXT [--args "CHECKMATE OPTIONS"] [--time 120]

import argparse
import concurrent.futures
import copy
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time


def physical_cores():
    try:
        cores = set()
        for block in open("/proc/cpuinfo").read().split("\n\n"):
            ids = dict(l.split(":", 1) for l in block.split("\n") if ":" in l)
            ids = {k.strip(): v.strip() for k, v in ids.items()}
            if "core id" in ids:
                cores.add((ids.get("physical id"), ids["core id"]))
        return len(cores) or os.cpu_count() or 1
    except OSError:
        return os.cpu_count() or 1


# ---- the tree ----

def find(game, path):
    node = game["tree"]
    for a in path:
        node = next(c["child"] for c in node["children"] if c["action"] == a)
    return node


def nodes(tree, path=()):
    yield path, tree
    for c in tree.get("children", []):
        yield from nodes(c["child"], path + (c["action"],))


def leaves(tree, path=()):
    if "children" not in tree:
        yield path
        return
    for c in tree["children"]:
        yield from leaves(c["child"], path + (c["action"],))


def size(game):
    return sum(1 for _ in nodes(game["tree"])), len(json.dumps(game))


def tidy(game):
    """Drop honest histories that left the tree; None if none is left (unless the game has honest utilities)."""
    ends = set(leaves(game["tree"]))
    if "honest_histories" in game:
        game["honest_histories"] = [h for h in game["honest_histories"]
                                    if all(isinstance(a, str) for a in h) and tuple(h) in ends]
        if not game["honest_histories"] and not game.get("honest_utilities"):
            return None
    return game


def without_branches(game, branches):
    """The game without the branches (parent path, action); None if a node would lose all its children."""
    g = copy.deepcopy(game)
    for parent, action in branches:
        try:
            node = find(g, parent)
        except StopIteration:
            continue
        node["children"] = [c for c in node["children"] if c["action"] != action]
        if not node["children"]:
            return None
    return tidy(g)


# ---- the candidates, coarse to fine ----

def removable(game):
    return [(p, c["action"]) for p, n in nodes(game["tree"]) if len(n.get("children", [])) > 1 for c in n["children"]]


def branch_chunks(game, granularity):
    units = removable(game)
    if granularity > len(units):
        return []
    step = -(-len(units) // granularity)
    return [lambda chunk=units[i:i + step]: without_branches(game, chunk) for i in range(0, len(units), step)]


def hoists(game):
    """Replace a node by one of its subtrees, largest cut first."""
    result = []
    for path, node in nodes(game["tree"]):
        for c in node.get("children", []):
            def hoist(path=path, action=c["action"]):
                g = copy.deepcopy(game)
                node = find(g, path)
                sub = next(x["child"] for x in node["children"] if x["action"] == action)
                node.clear()
                node.update(sub)
                return tidy(g)
            cut = sum(1 for _ in nodes(node)) - sum(1 for _ in nodes(c["child"]))
            result.append((-cut, len(result), hoist))
    return [h for _, _, h in sorted(result)]


def drops(game):
    """Drop an honest history, an initial or a property constraint."""
    result = []
    for key in ("honest_histories", "initial_constraints"):
        for i in range(len(game.get(key, [])) if key != "honest_histories" or len(game.get(key, [])) > 1 else 0):
            result.append(lambda key=key, i=i: {**game, key: game[key][:i] + game[key][i + 1:]})
    for prop, cs in game.get("property_constraints", {}).items():
        for i in range(len(cs)):
            result.append(lambda prop=prop, i=i: {**game, "property_constraints":
                                                  {**game["property_constraints"], prop: cs[:i] + cs[i + 1:]}})
    return result


def simpler_utilities(game):
    """Set a payoff to 0, or drop one of its terms."""
    result = []
    for path, node in nodes(game["tree"]):
        for j, u in enumerate(node.get("utility", [])):
            value = str(u["value"])
            terms = [t.strip() for t in re.split(r"(?=[+-])", value.replace(" ", "")) if t.strip()]
            options = ["0"] + (["".join(t for k, t in enumerate(terms) if k != i).lstrip("+") or "0"
                                for i in range(len(terms))] if len(terms) > 1 else [])
            for o in options:
                if o == value.replace(" ", ""):
                    continue

                def simpler(path=path, j=j, o=o):
                    g = copy.deepcopy(game)
                    find(g, path)["utility"][j]["value"] = o
                    return g
                result.append(simpler)
    return result


def cleanup(game):
    """Declare only the names that are used, and only the actions in the tree."""
    g = copy.deepcopy(game)
    used = set(re.findall(r"[A-Za-z_]\w*", json.dumps([g["tree"], g.get("initial_constraints", []),
                                                       g.get("property_constraints", {})])))
    for key in ("constants", "infinitesimals"):
        if isinstance(g.get(key), list):
            g[key] = [x for x in g[key] if x in used]
    seen = []
    for _, n in nodes(g["tree"]):
        for c in n.get("children", []):
            if c["action"] not in seen:
                seen.append(c["action"])
    g["actions"] = seen
    return g


# ---- reducing ----

class Reducer:
    def __init__(self, args):
        self.args, self.deadline = args, time.time() + args.time
        self.dir = tempfile.mkdtemp(prefix="reduce-")
        self.pool = concurrent.futures.ThreadPoolExecutor(args.jobs)
        self.counter, self.runs = 0, 0

    def interesting(self, game):
        """Does checkmate on `game` still print the text? A timeout counts as no."""
        left = self.deadline - time.time()
        if game is None or left <= 0:
            return False
        self.counter += 1
        path = os.path.join(self.dir, "candidate%d.json" % self.counter)
        with open(path, "w") as f:
            json.dump(game, f)
        try:
            p = subprocess.run([self.args.checkmate, path] + shlex.split(self.args.args), stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, universal_newlines=True, timeout=min(self.args.timeout, left))
            return self.args.grep in p.stdout
        except subprocess.TimeoutExpired:
            return False
        finally:
            self.runs += 1
            os.unlink(path)

    def first(self, makers):
        """The first game made by `makers` (in their order) that is still interesting, trying `jobs` at once."""
        for i in range(0, len(makers), self.args.jobs):
            if time.time() >= self.deadline:
                return None
            games = [m() for m in makers[i:i + self.args.jobs]]
            results = list(self.pool.map(self.interesting, games))
            for game, ok in zip(games, results):
                if ok:
                    return game
        return None

    def save(self, game):
        tmp = self.args.output + ".tmp"
        with open(tmp, "w") as f:
            json.dump(game, f, indent=2)
        os.replace(tmp, self.args.output)

    def run(self, game):
        start = time.time()
        self.save(game)
        print("start: %d nodes, %d bytes" % size(game), flush=True)
        progress = True
        while progress and time.time() < self.deadline:
            progress = False
            granularity = 2
            while True:
                smaller = self.first(branch_chunks(game, granularity))
                if smaller:
                    game, progress = smaller, True
                    granularity = max(granularity - 1, 2)
                    self.report(game, "branches", start)
                elif granularity < len(removable(game)) and time.time() < self.deadline:
                    granularity *= 2
                else:
                    break
            for name, kind in (("hoist", hoists), ("drop", drops), ("payoff", simpler_utilities)):
                while time.time() < self.deadline:
                    smaller = self.first(kind(game))
                    if not smaller:
                        break
                    game, progress = smaller, True
                    self.report(game, name, start)
        tidied = cleanup(game)
        if tidied != game and self.interesting(tidied):
            game = tidied
            self.save(game)
        self.pool.shutdown()
        os.rmdir(self.dir)
        print("%s: %d nodes, %d bytes in %s (%d runs, %.1f s)" % (
            "time is up" if time.time() >= self.deadline else "done", *size(game), self.args.output, self.runs,
            time.time() - start), flush=True)

    def report(self, game, step, start):
        self.save(game)
        print("%6.1f s  %-8s %d nodes, %d bytes" % (time.time() - start, step, *size(game)), flush=True)


def main():
    ap = argparse.ArgumentParser(description="Shrink a game while checkmate's output still contains a text.")
    ap.add_argument("game")
    ap.add_argument("output")
    ap.add_argument("--grep", required=True, help="text in checkmate's output (stdout and stderr) to keep")
    ap.add_argument("--args", default="", help="checkmate options, e.g. --collusion_resilience")
    ap.add_argument("--checkmate", default="build/checkmate")
    ap.add_argument("--time", type=float, default=120, help="seconds in all (default 120)")
    ap.add_argument("--timeout", type=float, default=2, help="seconds per checkmate run (default 2)")
    ap.add_argument("--jobs", "-j", type=int, default=physical_cores())
    args = ap.parse_args()
    game = json.load(open(args.game))
    reducer = Reducer(args)
    if not reducer.interesting(game):
        sys.exit("checkmate %s %s does not print %r (within %g s)" % (args.game, args.args, args.grep, args.timeout))
    reducer.run(game)


if __name__ == "__main__":
    main()
