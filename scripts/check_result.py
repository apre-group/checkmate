#!/usr/bin/env python3
# Independently check checkmate's --json-out results against the game.
# Usage: check_result.py game.json result.json [--complete-cases]
# Exit 0: CORRECT, 1: INCORRECT, 2: could not decide (solver timeout).

import argparse
import itertools
import json
import re
import sys
from fractions import Fraction

import z3

TIMEOUT_MS = 10000


class U:
    """A utility: real part plus infinitesimal part, compared lexicographically."""

    def __init__(self, real, inf):
        self.r, self.i = real, inf

    @staticmethod
    def of(x):
        return x if isinstance(x, U) else U(z3.RealVal(x), z3.RealVal(0))

    def __add__(self, o):
        o = U.of(o)
        return U(self.r + o.r, self.i + o.i)

    __radd__ = __add__

    def __sub__(self, o):
        o = U.of(o)
        return U(self.r - o.r, self.i - o.i)

    def __rsub__(self, o):
        return U.of(o) - self

    def __neg__(self):
        return U(-self.r, -self.i)

    def __mul__(self, o):
        o = U.of(o)
        return U(self.r * o.r, self.i * o.r + self.r * o.i)

    __rmul__ = __mul__

    def __lt__(self, o):
        o = U.of(o)
        return z3.Or(self.r < o.r, z3.And(self.r == o.r, self.i < o.i))

    def __le__(self, o):
        o = U.of(o)
        return z3.Or(self.r < o.r, z3.And(self.r == o.r, self.i <= o.i))

    def __gt__(self, o):
        return U.of(o) < self

    def __ge__(self, o):
        return U.of(o) <= self

    def __eq__(self, o):
        o = U.of(o)
        return z3.And(self.r == o.r, self.i == o.i)

    def __ne__(self, o):
        return z3.Not(self == o)


def zero():
    return U.of(0)


class Parser:
    def __init__(self, constants, infinitesimals):
        self.env = {}
        for c in constants:
            self.env[c] = U(z3.Real(c), z3.RealVal(0))
        for e in infinitesimals:
            self.env[e] = U(z3.RealVal(0), z3.Real(e))
        self.env["N"] = lambda s: U.of(Fraction(s))
        self.raw_env = {n: z3.Real(n) for n in constants + infinitesimals}
        self.raw_env["N"] = lambda s: z3.RealVal(Fraction(s))

    def _py(self, s):
        s = re.sub(r"(?<![\w.])(\d+(\.\d+)?)", r'N("\1")', s)
        s = s.replace("!=", "#").replace("<=", "{").replace(">=", "}")
        s = s.replace("=", "==").replace("#", "!=").replace("{", "<=").replace("}", ">=")
        return s

    def utility(self, s):
        return U.of(eval(self._py(str(s)), {"__builtins__": {}}, self.env))

    def raw_case(self, s):
        """A case condition as printed in subtree results: fully parenthesized, over plain reals."""
        if s == "true":
            return z3.BoolVal(True)
        return eval(self._py(s), {"__builtins__": {}}, self.raw_env)

    def constraint(self, s):
        # `|` binds looser than comparisons in the input grammar, unlike Python
        return z3.Or([eval(self._py(p), {"__builtins__": {}}, self.env) for p in s.split("|")])


class Node:
    def __init__(self, hist):
        self.hist = hist
        self.player = None
        self.children = []  # (action, Node)
        self.u = None       # player -> U, for leaves
        self.sub = None     # parsed result, for subtree nodes
        self.cond = None    # for the virtual leaves of a subtree: the case its utility is practical in
        self.parent = None

    def is_leaf(self):
        return self.u is not None

    def is_subtree(self):
        return self.sub is not None

    def child(self, action):
        for a, c in self.children:
            if a == action:
                return c
        return None

    def leaves(self):
        if self.is_leaf():
            return [self]
        if self.is_subtree():
            return self.sub["virtual_leaves"]
        return [l for _, c in self.children for l in c.leaves()]


def load_subtree(j, parser, n):
    def cases(entries):
        return {frozenset(e["player_group"]): z3.Or([z3.And([parser.raw_case(c) for c in case])
                                                     for case in e["satisfied_in_case"]])
                for e in entries}
    utility = lambda entries: {e["player"]: parser.utility(e["value"]) for e in entries}
    n.sub = {
        "weak_immunity": cases(j["weak_immunity"]),
        "weaker_immunity": cases(j["weaker_immunity"]),
        "collusion_resilience": cases(j["collusion_resilience"]),
        "practicality": [(z3.And([parser.raw_case(c) for c in e["case"]]), [utility(u) for u in e["utilities"]])
                         for e in j["practicality"]],
        "honest_utility": utility(j["honest_utility"]),
        "virtual_leaves": [],
    }
    for i, (cond, us) in enumerate(n.sub["practicality"]):
        for k, u in enumerate(us):
            v = Node(n.hist + ("#%d.%d" % (i, k),))
            v.u, v.cond, v.parent = u, cond, n
            n.sub["virtual_leaves"].append(v)


def load_tree(j, parser, hist=()):
    n = Node(hist)
    if "utility" in j:
        n.u = {e["player"]: parser.utility(e["value"]) for e in j["utility"]}
    elif "children" in j:
        n.player = j["player"]
        n.children = [(c["action"], load_tree(c["child"], parser, hist + (c["action"],)))
                      for c in j["children"]]
    else:
        load_subtree(j["subtree"], parser, n)
    return n


class Unsupported(Exception):
    pass


class Unknown(Exception):
    pass


class Checker:
    def __init__(self, game):
        self.parser = Parser(game["constants"], game["infinitesimals"])
        self.players = sorted(game["players"])
        self.root = load_tree(game["tree"], self.parser)
        self.initial = [self.parser.constraint(c) for c in game["initial_constraints"]]
        self.prop_constraints = {p: [self.parser.constraint(c) for c in cs]
                                 for p, cs in game["property_constraints"].items()}
        self.decls = "".join("(declare-const %s Real)" % n
                             for n in game["constants"] + game["infinitesimals"])
        self.errors = []
        self.unknown = []
        self.queries = 0

    def smt2(self, s):
        return z3.parse_smt2_string(self.decls + "(assert %s)" % s)[0]

    def node(self, hist):
        """The node at `hist`; a subtree node stands for everything below it."""
        n = self.root
        for a in hist:
            if n.is_leaf():
                return None
            if n.is_subtree():
                return n
            n = n.child(a)
            if n is None:
                return None
        return n

    def check(self, assumptions, *formulas):
        self.queries += 1
        s = z3.Solver()
        s.set("timeout", TIMEOUT_MS)
        s.add(*assumptions)
        s.add(*formulas)
        r = s.check()
        if r == z3.unknown:
            raise Unknown(s.reason_unknown())
        return r == z3.sat

    def valid(self, assumptions, formula):
        return not self.check(assumptions, z3.Not(formula))

    def error(self, ctx, msg):
        self.errors.append("%s: %s" % (ctx, msg))

    # ---- semantics -------------------------------------------------------

    def on_honest(self, n, honest):
        return len(n.hist) < len(honest) and tuple(honest[:len(n.hist)]) == n.hist

    def sub_entry(self, n, prop, group):
        f = n.sub[prop].get(frozenset(group))
        if f is None:
            self.error("subtree at %s" % list(n.hist), "no %s result for %s" % (prop, sorted(group)))
            return z3.BoolVal(False)
        return f

    def utility_at(self, n):
        """Utility at the end of the honest history: a leaf's, or the honest utility of a subtree."""
        return n.u if n.is_leaf() else n.sub["honest_utility"]

    def wi_ok(self, leaf, p, weaker):
        return leaf.u[p].r >= 0 if weaker else leaf.u[p] >= zero()

    def wi_formula(self, n, p, honest, weaker):
        if n.is_leaf():
            return self.wi_ok(n, p, weaker)
        if n.is_subtree():
            return self.sub_entry(n, "weaker_immunity" if weaker else "weak_immunity", [p])
        if n.player == p and self.on_honest(n, honest):
            return self.wi_formula(n.child(honest[len(n.hist)]), p, honest, weaker)
        subs = [self.wi_formula(c, p, honest, weaker) for _, c in n.children]
        return z3.Or(subs) if n.player == p else z3.And(subs)

    def groups(self):
        k = len(self.players)
        for size in range(1, k):
            for g in itertools.combinations(self.players, size):
                yield frozenset(g)

    def gsum(self, leaf_u, g):
        s = zero()
        for p in g:
            s = s + leaf_u[p]
        return s

    def cr_formula(self, honest, honest_u, entry_group=frozenset()):
        # exists a strategy (selectors at off-honest nodes) such that no group gains;
        # entry_group: players that already deviated before reaching this tree
        sel = {}
        conds = []

        def walk(n, path):
            if n.is_leaf():
                for g in self.groups():
                    if not entry_group <= g:
                        continue
                    reach = [c for (actor, c) in path if actor not in g]
                    conds.append(z3.Implies(z3.And(reach) if reach else z3.BoolVal(True),
                                            self.gsum(n.u, g) <= self.gsum(honest_u, g)))
                return
            if n.is_subtree():
                # The entry for the players that actually deviated on the way here: one strategy inside
                # the subtree against all their supergroups (not each supergroup with its own strategy).
                dev = {p: z3.Or([z3.Not(c) for (actor, c) in path if actor == p]) for p in self.players}
                for size in range(len(self.players) + 1):
                    for d in itertools.combinations(self.players, size):
                        deviators = entry_group | frozenset(d)
                        if len(deviators) == len(self.players):
                            continue
                        exactly = z3.And([dev[p] if p in d else z3.Not(dev[p]) for p in self.players])
                        conds.append(z3.Implies(exactly, self.sub_entry(n, "collusion_resilience", deviators)))
                return
            if self.on_honest(n, honest):
                h = honest[len(n.hist)]
                for a, c in n.children:
                    walk(c, path + [(n.player, z3.BoolVal(a == h))])
                return
            v = z3.Int("sel_%d" % len(sel))
            sel[n.hist] = v
            conds.append(z3.And(v >= 0, v < len(n.children)))
            for i, (a, c) in enumerate(n.children):
                walk(c, path + [(n.player, v == i)])

        walk(self.root, [])
        body = z3.And(conds)
        return z3.Exists(list(sel.values()), body) if sel else body

    def spe_outcome(self, n, leaf, memo):
        """Formula: some subgame perfect profile of the subgame at n ends in `leaf`."""
        key = (n.hist, leaf.hist)
        if key in memo:
            return memo[key]
        if n.is_leaf():
            f = z3.BoolVal(n is leaf)
        elif n.is_subtree():
            f = leaf.cond if leaf.parent is n else z3.BoolVal(False)
        else:
            a = leaf.hist[len(n.hist)]
            parts = [self.spe_outcome(n.child(a), leaf, memo)]
            for b, c in n.children:
                if b != a:
                    parts.append(self.not_better(c, n.player, leaf.u[n.player], memo))
            f = z3.And(parts)
        memo[key] = f
        return f

    def not_better(self, n, q, bound, memo):
        """Formula: the subgame at n has a subgame perfect outcome giving q at most `bound`."""
        return z3.Or([z3.And(self.spe_outcome(n, l, memo), l.u[q] <= bound) for l in n.leaves()])

    def pr_formula(self, honest, honest_leaf):
        memo = {}
        parts = []
        hu = self.utility_at(honest_leaf)
        n = self.root
        for a in honest:
            if n.is_subtree():
                break
            for b, c in n.children:
                if b != a:
                    parts.append(self.not_better(c, n.player, hu[n.player], memo))
            n = n.child(a)
        if n.is_subtree():
            # along the honest history, the subtree result lists the cases its honest history is practical in
            parts.append(z3.Or([cond for cond, _ in n.sub["practicality"]]))
        return z3.And(parts) if parts else z3.BoolVal(True)

    def property_formula(self, prop, honest, honest_leaf):
        if prop in ("weak_immunity", "weaker_immunity"):
            weaker = prop == "weaker_immunity"
            return z3.And([self.wi_formula(self.root, p, honest, weaker) for p in self.players])
        if prop == "collusion_resilience":
            return self.cr_formula(honest, self.utility_at(honest_leaf))
        return self.pr_formula(honest, honest_leaf)

    # ---- certificates ----------------------------------------------------

    def strategy_map(self, ctx, strategy, honest):
        s = {}
        for e in strategy:
            n = self.node(e["history"])
            h = tuple(e["history"])
            if n is None or n.is_leaf() or n.is_subtree():
                self.error(ctx, "strategy names non-branch history %s" % (e["history"],))
                continue
            if n.player != e["player"] or n.child(e["action"]) is None:
                self.error(ctx, "strategy entry %s is not a legal move" % (e,))
                continue
            if h in s and s[h] != e["action"]:
                self.error(ctx, "strategy has two actions at %s" % (e["history"],))
            if self.on_honest(n, honest) and e["action"] != honest[len(h)]:
                self.error(ctx, "strategy leaves the honest history at %s" % (e["history"],))
            s[h] = e["action"]
        return s

    def check_wi_strategy(self, ctx, assume, s, honest, weaker):
        for p in self.players:
            def walk(n):
                if n.is_leaf():
                    if not self.valid(assume, self.wi_ok(n, p, weaker)):
                        self.error(ctx, "strategy: %s can be harmed at %s" % (p, list(n.hist)))
                    return
                if n.is_subtree():
                    entry = self.sub_entry(n, "weaker_immunity" if weaker else "weak_immunity", [p])
                    if not self.valid(assume, entry):
                        self.error(ctx, "strategy: %s can be harmed in the subtree at %s" % (p, list(n.hist)))
                    return
                if n.player == p and self.on_honest(n, honest):
                    walk(n.child(honest[len(n.hist)]))
                elif n.player == p and n.hist in s:
                    walk(n.child(s[n.hist]))
                else:
                    for _, c in n.children:
                        walk(c)
            walk(self.root)

    def check_cr_strategy(self, ctx, assume, s, honest, honest_u):
        def walk(n, deviators):
            if n.is_leaf():
                for g in self.groups():
                    if deviators <= g and not self.valid(assume, self.gsum(n.u, g) <= self.gsum(honest_u, g)):
                        self.error(ctx, "strategy: group %s gains at %s" % (sorted(g), list(n.hist)))
                return
            if n.is_subtree():
                if len(deviators) < len(self.players) and \
                        not self.valid(assume, self.sub_entry(n, "collusion_resilience", deviators)):
                    self.error(ctx, "strategy: the subtree at %s is not resilient against supergroups of %s"
                               % (list(n.hist), sorted(deviators)))
                return
            fixed = honest[len(n.hist)] if self.on_honest(n, honest) else s.get(n.hist)
            for a, c in n.children:
                walk(c, deviators | {n.player} if fixed is not None and a != fixed else deviators)
        walk(self.root, frozenset())

    def check_pr_strategy(self, ctx, assume, s, honest):
        # strategies end at subtrees, whose outcome is not known here: those comparisons are skipped
        def outcome(n):
            while not n.is_leaf() and not n.is_subtree():
                if n.hist not in s:
                    return None
                n = n.child(s[n.hist])
            return n

        def walk(n):
            if n.is_leaf() or n.is_subtree():
                return
            out = outcome(n)
            if out is None:
                self.error(ctx, "practicality strategy is incomplete below %s" % (list(n.hist),))
                return
            for a, c in n.children:
                oc = outcome(c)
                if oc is not None and oc.is_leaf() and out.is_leaf() and not self.valid(assume, oc.u[n.player] <= out.u[n.player]):
                    self.error(ctx, "strategy: %s gains by playing %s at %s" % (n.player, a, list(n.hist)))
                walk(c)
        walk(self.root)

    def ce_map(self, ctx, choices):
        m = {}
        for e in choices:
            n = self.node(e["history"])
            if n is None or n.is_leaf() or n.is_subtree():
                self.error(ctx, "counterexample names non-branch history %s" % (e["history"],))
                continue
            if n.player != e["player"] or any(n.child(a) is None for a in e["actions"]) or not e["actions"]:
                self.error(ctx, "counterexample entry %s is not a legal move" % (e,))
                continue
            m[tuple(e["history"])] = e["actions"]
        return m

    def check_wi_ce(self, ctx, assume, ce, honest, weaker):
        if len(ce["player_group"]) != 1:
            self.error(ctx, "weak immunity counterexample without exactly one harmed player")
            return
        p = ce["player_group"][0]
        m = self.ce_map(ctx, ce["choices"])

        def walk(n):
            if n.is_leaf():
                if not self.valid(assume, z3.Not(self.wi_ok(n, p, weaker))):
                    self.error(ctx, "counterexample: %s is not harmed at %s" % (p, list(n.hist)))
                return
            if n.is_subtree():
                entry = self.sub_entry(n, "weaker_immunity" if weaker else "weak_immunity", [p])
                if not self.valid(assume, z3.Not(entry)):
                    self.error(ctx, "counterexample: %s is not harmed in the subtree at %s" % (p, list(n.hist)))
                return
            if n.player == p:
                if n.hist in m:
                    self.error(ctx, "counterexample prescribes moves to the harmed player")
                if self.on_honest(n, honest):
                    walk(n.child(honest[len(n.hist)]))
                else:
                    for _, c in n.children:
                        walk(c)
            elif n.hist in m:
                for a in m[n.hist]:
                    walk(n.child(a))
            elif self.on_honest(n, honest):
                walk(n.child(honest[len(n.hist)]))
            else:
                for _, c in n.children:
                    walk(c)
        walk(self.root)

    def check_cr_ce(self, ctx, assume, ce, honest, honest_u):
        m = self.ce_map(ctx, ce["choices"])
        # without a deviation, the honest history itself has to end in a subtree that is not resilient
        if not ce["choices"]:
            if not self.node(honest).is_subtree():
                self.error(ctx, "collusion resilience counterexample without a deviation")
                return
        else:
            first = ce["choices"][0]
            dev_node = self.node(first["history"])
            if dev_node is None or not self.on_honest(dev_node, honest) or honest[len(dev_node.hist)] in first["actions"]:
                self.error(ctx, "counterexample does not start with a deviation from the honest history")
                return
        claimed = {tuple(l["history"]): [frozenset(g) for g in l["groups"]] for l in ce["cr_leaves"]}
        reached = set()

        def walk(n, deviators, deviated):
            if n.is_subtree():
                reached.add(n.hist)
                entry = next((l for l in ce["cr_leaves"] if tuple(l["history"]) == n.hist), None)
                if entry is None or not entry["subtree"]:
                    self.error(ctx, "counterexample reaches the subtree at %s but does not list it" % (list(n.hist),))
                    return
                g = frozenset(entry["groups"][0])
                if not deviators <= g:
                    self.error(ctx, "counterexample: group %s at the subtree misses deviators %s" % (sorted(g), sorted(deviators)))
                if not self.valid(assume, z3.Not(self.sub_entry(n, "collusion_resilience", g))):
                    self.error(ctx, "counterexample: the subtree at %s is resilient against group %s" % (list(n.hist), sorted(g)))
                return
            if n.is_leaf():
                reached.add(n.hist)
                groups = claimed.get(n.hist)
                if groups is None:
                    self.error(ctx, "counterexample reaches %s but lists no group for it" % (list(n.hist),))
                    return
                ok = False
                for g in groups:
                    if len(g) == len(self.players):
                        self.error(ctx, "counterexample group %s is all players" % sorted(g))
                    gains = self.valid(assume, self.gsum(n.u, g) > self.gsum(honest_u, g))
                    if not gains:
                        self.error(ctx, "counterexample: group %s does not gain at %s" % (sorted(g), list(n.hist)))
                    ok = ok or (gains and deviators <= g)
                if not ok:
                    self.error(ctx, "counterexample: no listed group containing the deviators %s gains at %s"
                               % (sorted(deviators), list(n.hist)))
                return
            if n.hist in m:
                for a in m[n.hist]:
                    walk(n.child(a), deviators | {n.player}, True)
            elif not deviated:
                walk(n.child(honest[len(n.hist)]), deviators, False)
            else:
                for _, c in n.children:
                    walk(c, deviators, True)
        walk(self.root, frozenset(), False)
        if not ce["cr_more_omitted"]:
            for h in claimed:
                if h not in reached:
                    self.error(ctx, "counterexample lists unreachable leaf %s" % (list(h),))

    def check_pr_ce(self, ctx, assume, ce, honest, honest_leaf):
        if not ce["player_group"]:
            n = self.node(ce["choices"][0]["history"])
            if n is None or not n.is_subtree():
                self.error(ctx, "practicality counterexample names a subtree that is not there")
            elif not self.valid(assume, z3.Not(z3.Or([cond for cond, _ in n.sub["practicality"]]))):
                self.error(ctx, "the subtree at %s is practical in some part of the case" % (list(n.hist),))
            return
        q = ce["player_group"][0]
        h = ce["choices"][0]["history"]
        dev = self.node(h[:-1]) if h else None
        if dev is None or not self.on_honest(dev, honest) or dev.player != q or honest[len(h) - 1] == h[-1]:
            self.error(ctx, "practicality counterexample is not a deviation of %s from the honest history" % q)
            return
        sub = dev.child(h[-1])
        if sub is None:
            self.error(ctx, "practicality counterexample deviates to unknown action")
            return
        hu = self.utility_at(honest_leaf)
        for e in ce["choices"]:
            leaf = self.node(h + e["actions"])
            if leaf is not None and leaf.is_subtree():
                continue
            if leaf is None or not leaf.is_leaf():
                self.error(ctx, "practical history %s does not end in a leaf" % (h + e["actions"],))
            elif not self.valid(assume, leaf.u[q] > hu[q]):
                self.error(ctx, "practical history %s is not better for %s" % (h + e["actions"], q))
        if self.check(assume, self.not_better(sub, q, hu[q], {})):
            self.error(ctx, "some subgame perfect outcome after %s is not better for %s" % (h, q))

    # ---- subtree results ---------------------------------------------------

    def smt2_utility(self, entries):
        def real(e):
            return z3.parse_smt2_string(self.decls + "(assert (= %s 0.0))" % e)[0].arg(0)
        return {e["player"]: U(real(e["real"]), real(e["infinitesimal"])) for e in entries}

    def same_utility(self, a, b):
        return z3.And([a[p] == b[p] for p in self.players])

    def check_regions(self, ctx, base, cases, formula):
        """The listed cases must be exactly where `formula` holds: unlisted cases count as violated."""
        conds = []
        for c in cases:
            cc = [self.smt2(x) for x in c]
            conds.append(z3.And(cc) if cc else z3.BoolVal(True))
            if not self.check(base + cc):
                self.error(ctx, "case %s is unsatisfiable" % c)
            elif self.check(base + cc, z3.Not(formula)):
                self.error(ctx, "case %s is listed as satisfied, but the property fails somewhere in it" % c)
        if self.check(base, formula, z3.Not(z3.Or(conds) if conds else z3.BoolVal(False))):
            self.error(ctx, "the property holds somewhere outside the listed cases")

    def check_subtree(self, game, res):
        along = bool(game.get("honest_histories"))
        honest = game["honest_histories"][0] if along else []
        if along:
            leaf = self.node(honest)
            if leaf is None or not (leaf.is_leaf() or leaf.is_subtree()):
                self.error("subtree", "honest history does not end in a leaf")
                return
            honest_u = self.utility_at(leaf)
        else:
            honest_u = {e["player"]: self.parser.utility(e["value"]) for e in game["honest_utilities"][0]["utility"]}
        base_all = self.initial
        if not self.valid(base_all, self.same_utility(self.smt2_utility(res["honest_utility"]), honest_u)):
            self.error("subtree", "honest_utility differs from the honest leaf")

        for prop in ("weak_immunity", "weaker_immunity"):
            base = self.initial + self.prop_constraints.get(prop, [])
            for e in res[prop]:
                p = e["player_group"][0]
                ctx = "subtree %s for %s" % (prop, p)
                try:
                    self.check_regions(ctx, base, e["satisfied_in_case"],
                                       self.wi_formula(self.root, p, honest, prop == "weaker_immunity"))
                except Unknown as u:
                    self.unknown.append("%s: %s" % (ctx, u))

        base = self.initial + self.prop_constraints.get("collusion_resilience", [])
        for e in res["collusion_resilience"]:
            ctx = "subtree collusion_resilience against group %s" % e["player_group"]
            try:
                self.check_regions(ctx, base, e["satisfied_in_case"],
                                   self.cr_formula(honest, honest_u, frozenset(e["player_group"])))
            except Unknown as u:
                self.unknown.append("%s: %s" % (ctx, u))

        base = self.initial + self.prop_constraints.get("practicality", [])
        try:
            if along:
                ctx = "subtree practicality"
                for e in res["practicality"]:
                    if len(e["utilities"]) != 1 or not self.valid(base, self.same_utility(self.smt2_utility(e["utilities"][0]), honest_u)):
                        self.error(ctx, "case %s does not list exactly the honest utility" % e["case"])
                self.check_regions(ctx, base, [e["case"] for e in res["practicality"]],
                                   self.pr_formula(honest, self.node(honest)))
            else:
                self.check_practical_utilities(base, res["practicality"])
        except Unknown as u:
            self.unknown.append("subtree practicality: %s" % u)

    def check_practical_utilities(self, base, entries):
        ctx = "subtree practicality"
        memo = {}
        leaves = self.root.leaves()
        conds = []
        for e in entries:
            cc = [self.smt2(x) for x in e["case"]]
            conds.append(z3.And(cc) if cc else z3.BoolVal(True))
            assume = base + cc
            listed = [self.smt2_utility(u) for u in e["utilities"]]
            if not self.check(assume):
                self.error(ctx, "case %s is unsatisfiable" % e["case"])
                continue
            for u in listed:
                outcome = z3.Or([z3.And(self.spe_outcome(self.root, l, memo), self.same_utility(l.u, u)) for l in leaves])
                if not self.valid(assume, outcome):
                    self.error(ctx, "case %s lists a utility that is not always a subgame perfect outcome" % e["case"])
            for l in leaves:
                others = [z3.Not(self.same_utility(l.u, u)) for u in listed]
                if self.check(assume, self.spe_outcome(self.root, l, memo), *others):
                    self.error(ctx, "case %s misses the subgame perfect outcome %s" % (e["case"], list(l.hist)))
        if self.check(base, z3.Not(z3.Or(conds) if conds else z3.BoolVal(False))):
            self.error(ctx, "cases do not cover the constraints")

    # ---- driver ----------------------------------------------------------

    def check_result(self, r, complete_cases):
        if r["history"] is None:
            raise Unsupported("results without honest history")
        prop = r["property"]
        honest = r["history"]
        ctx = "%s %s" % (honest, prop)
        honest_leaf = self.node(honest)
        if honest_leaf is None or not (honest_leaf.is_leaf() or honest_leaf.is_subtree()):
            self.error(ctx, "honest history does not end in a leaf")
            return
        base = self.initial + self.prop_constraints.get(prop, [])
        formula = self.property_formula(prop, honest, honest_leaf)

        cases = []
        for c in r["cases"]:
            conds = [self.smt2(s) for s in c["case"]]
            cases.append(conds)
            assume = base + conds
            cctx = "%s case %s" % (ctx, c["case"])
            if not self.check(assume):
                self.error(cctx, "case is unsatisfiable")
                continue
            if c["holds"] and self.check(assume, z3.Not(formula)):
                self.error(cctx, "case marked as holding, but the property fails somewhere in it")
            if not c["holds"] and self.check(assume, formula):
                self.error(cctx, "case marked as violated, but the property holds somewhere in it")

        if r["holds"] or complete_cases:
            covered = z3.Or([z3.And(c) if c else z3.BoolVal(True) for c in cases])
            if self.check(base, z3.Not(covered)):
                self.error(ctx, "cases do not cover the constraints")

        if "precondition" in r:
            pre = self.smt2(r["precondition"])
            if self.check(base, pre, z3.Not(formula)):
                self.error(ctx, "the property fails somewhere under the weakest precondition %s" % r["precondition"])
            if self.check(base, formula, z3.Not(pre)):
                self.error(ctx, "the precondition %s is not weakest: the property holds somewhere outside it"
                           % r["precondition"])

        weaker = prop == "weaker_immunity"
        for st in r["strategies"]:
            assume = base + [self.smt2(s) for s in st["case"]]
            sctx = "%s strategy for case %s" % (ctx, st["case"])
            s = self.strategy_map(sctx, st["strategy"], honest)
            if prop in ("weak_immunity", "weaker_immunity"):
                self.check_wi_strategy(sctx, assume, s, honest, weaker)
            elif prop == "collusion_resilience":
                self.check_cr_strategy(sctx, assume, s, honest, self.utility_at(honest_leaf))
            else:
                self.check_pr_strategy(sctx, assume, s, honest)

        for ce in r["counterexamples"]:
            assume = base + [self.smt2(s) for s in ce["case"]]
            cctx = "%s counterexample for case %s" % (ctx, ce["case"])
            if not self.check(assume):
                self.error(cctx, "counterexample case is unsatisfiable")
                continue
            if prop in ("weak_immunity", "weaker_immunity"):
                self.check_wi_ce(cctx, assume, ce, honest, weaker)
            elif prop == "collusion_resilience":
                self.check_cr_ce(cctx, assume, ce, honest, self.utility_at(honest_leaf))
            else:
                self.check_pr_ce(cctx, assume, ce, honest, honest_leaf)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("game")
    ap.add_argument("result")
    ap.add_argument("--complete-cases", action="store_true",
                    help="checkmate ran with --all_cases, so cases must cover the constraints")
    ap.add_argument("--subtree", action="store_true", help="result is from checkmate --subtree --json-out")
    args = ap.parse_args()
    game = json.load(open(args.game))
    if args.subtree:
        results = [json.load(open(args.result))["subtree"]]
    else:
        results = json.load(open(args.result))["results"]
    try:
        checker = Checker(game)
        if args.subtree:
            checker.check_subtree(game, results[0])
        for r in ([] if args.subtree else results):
            try:
                checker.check_result(r, args.complete_cases)
            except Unknown as e:
                checker.unknown.append("%s %s: %s" % (r["history"], r["property"], e))
    except Unsupported as e:
        print("UNSUPPORTED: %s" % e)
        sys.exit(0)
    for e in checker.errors:
        print("ERROR: " + e)
    if checker.errors:
        print("Results are INCORRECT")
        sys.exit(1)
    for u in checker.unknown:
        print("UNKNOWN: " + u)
    if checker.unknown:
        sys.exit(2)
    print("Results are CORRECT (%d results, %d queries)" % (len(results), checker.queries))
    sys.exit(0)


if __name__ == "__main__":
    main()
