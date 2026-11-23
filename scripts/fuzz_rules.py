#!/usr/bin/env python3
# Fuzz the rules compiler (scripts/rules.mjs): random rules are compiled, and the tree they give must be the one
# that playing them out here gives, with payoffs compared exactly at random values of the constants.
# Run from the repo root: scripts/fuzz_rules.py [--num N] [--seed S]

import argparse
import json
import os
import random
import re
import shlex
import subprocess
import sys
from fractions import Fraction

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPTS)
from fuzz import unique_file

MAX_DEPTH = 100


class Bug(Exception):
    pass


# an error the compiler must report: a part of its message, and its line
# a game too large to be worth comparing: the fuzzer goes on with the next one
class TooBig(Exception):
    pass


MAX_COMPARED = 2000


class Expected(Exception):
    def __init__(self, message, line):
        super().__init__(message)
        self.message, self.line = message, line


def run(cmd, check_rc=True, timeout=None):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,
                       timeout=timeout or args.tout)
    if p.returncode < 0 or (check_rc and p.returncode != 0):
        raise Bug("%s failed with %d:\n%s%s\ncommand: %s" % (cmd[0], p.returncode, p.stdout[-2000:], p.stderr[-2000:],
                                                           " ".join(shlex.quote(c) for c in cmd)))
    return p


# ---- expressions: ("num", Fraction), ("id", name), ("neg", e), ("not", e), ("bin", op, l, r) ----

PREC = {"or": 1, "and": 2, "=": 4, "!=": 4, "<": 4, "<=": 4, ">": 4, ">=": 4, "+": 5, "-": 5, "*": 6, "/": 6}


def show(e, rng, outer=0):
    """The expression as text, with the parentheses that precedence needs, and now and then more."""
    kind = e[0]
    if kind == "num":
        text, prec = str(e[1]) if e[1].denominator == 1 else "%g" % float(e[1]), 9
    elif kind == "id":
        text, prec = e[1], 9
    elif kind == "neg":
        # - applies to what follows directly: a name, a number, or parentheses
        text, prec = "-" + show(e[1], rng, 9), 9
    elif kind == "not":
        text, prec = "not " + show(e[1], rng, 3), 3
    else:
        op, prec = e[1], PREC[e[1]]
        # comparisons do not chain; the other operators group to the left
        right = prec + 1 if prec == 4 or op in ("-", "/", "+", "*", "and", "or") else prec
        text = "%s %s %s" % (show(e[2], rng, prec + 1 if prec == 4 else prec), op, show(e[3], rng, right))
    if prec < outer or (kind != "id" and kind != "num" and rng.random() < 0.1):
        text = "(" + text + ")"
    return text


MAX_NUMBER = 2**64


def value(e, env, line):
    """The value of a state expression: a bool, a Fraction, or a name. As in the compiler, and and or stop early,
    and a number larger than 2^64 is an error at `line`."""
    kind = e[0]
    if kind == "num":
        return e[1]
    if kind == "id":
        return env[e[1]]
    if kind == "neg":
        return -value(e[1], env, line)
    if kind == "not":
        return not value(e[1], env, line)
    op = e[1]
    if op == "and":
        return value(e[2], env, line) and value(e[3], env, line)
    if op == "or":
        return value(e[2], env, line) or value(e[3], env, line)
    l, r = value(e[2], env, line), value(e[3], env, line)
    if op in ("+", "-", "*"):
        v = {"+": lambda: l + r, "-": lambda: l - r, "*": lambda: l * r}[op]()
        if abs(v.numerator) > MAX_NUMBER or v.denominator > MAX_NUMBER:
            raise Expected("a number in the state gets larger than 2^64", line)
        return v
    return {"=": lambda: l == r, "!=": lambda: l != r, "<": lambda: l < r, "<=": lambda: l <= r,
            ">": lambda: l > r, ">=": lambda: l >= r}[op]()


def amount(e, env, point):
    """The value of a payoff expression at `point`, the values of the constants and infinitesimals."""
    kind = e[0]
    if kind == "num":
        return e[1]
    if kind == "id":
        return point[e[1]] if e[1] in point else env[e[1]]
    if kind == "neg":
        return -amount(e[1], env, point)
    op, l, r = e[1], amount(e[2], env, point), amount(e[3], env, point)
    return {"+": lambda: l + r, "-": lambda: l - r, "*": lambda: l * r, "/": lambda: l / r}[op]()


# ---- random rules ----

class Move:
    def __init__(self, name, players, honest, description):
        self.name, self.players, self.honest, self.description = name, players, honest, description
        self.conditions, self.sets, self.pays, self.end = [], [], [], False
        self.next: tuple | None = None
        # the lines of the move, its conditions, its set line, and its next line
        self.line, self.condition_lines, self.set_line, self.next_line = 0, [], 0, 0


def gen_rules(rng):
    players = rng.choice([["A", "B"], ["Ann", "Bob"], ["A", "B", "C"]])
    two = len(players) == 2
    constants = ["c%d" % i for i in range(rng.randint(1, 3))]
    infinitesimals = ["e%d" % i for i in range(rng.choice([0, 0, 1]))]
    bools = ["b%d" % i for i in range(rng.randint(0, 2))]
    ints = ["n%d" % i for i in range(rng.randint(0, 2))]
    phases = ["p0", "p1", "p2"] if rng.random() < 0.5 else []
    clock = rng.random() < 0.85
    limit = rng.randint(1, 4)
    state = {}
    for b in bools:
        state[b] = ("id", rng.choice(["yes", "no", "true", "false"]))
    for n in ints:
        state[n] = ("num", Fraction(rng.randint(0, 3)))
    if phases:
        state["ph"] = ("id", rng.choice(phases))
    if clock:
        state["t"] = ("num", Fraction(0))

    def num_expr(d):
        if d <= 0 or rng.random() < 0.5:
            return ("id", rng.choice(ints)) if ints and rng.random() < 0.6 else ("num", Fraction(rng.randint(0, 4)))
        if rng.random() < 0.1:
            return ("neg", num_expr(d - 1))
        return ("bin", rng.choice(["+", "-", "*"]), num_expr(d - 1), num_expr(d - 1))

    def bool_expr(d, in_move):
        options = ["lit", "cmp"] + (["var"] * 2 if bools else []) + (["phase"] if phases else []) + (["me"] if in_move else [])
        if d > 0:
            options += ["not", "and", "or"]
        kind = rng.choice(options)
        if kind == "lit":
            return ("id", rng.choice(["yes", "no"]))
        if kind == "var":
            return ("id", rng.choice(bools))
        if kind == "cmp":
            return ("bin", rng.choice(["<", "<=", ">", ">=", "=", "!="]), num_expr(1), num_expr(1))
        if kind == "phase":
            return ("bin", rng.choice(["=", "!="]), ("id", "ph"), ("id", rng.choice(phases)))
        if kind == "me":
            return ("bin", rng.choice(["=", "!="]), ("id", "me"), ("id", rng.choice(players)))
        if kind == "not":
            return ("not", bool_expr(d - 1, in_move))
        return ("bin", kind, bool_expr(d - 1, in_move), bool_expr(d - 1, in_move))

    def pay_expr(d):
        if d <= 0 or rng.random() < 0.35:
            r = rng.random()
            if r < 0.5:
                return ("id", rng.choice(constants + infinitesimals))
            if r < 0.65 and ints:
                return ("id", rng.choice(ints))
            return ("num", Fraction(rng.choice([0, 1, 2, 3, 10])) / rng.choice([1, 1, 2, 4, 5]))
        r = rng.random()
        if r < 0.1:
            return ("neg", pay_expr(d - 1))
        if r < 0.2:
            return ("bin", "/", pay_expr(d - 1), ("num", Fraction(rng.choice([1, 2, 4, 5, 8]))))
        if r < 0.35:
            # products of constants (CheckMate does not multiply infinitesimals with each other)
            factor = ("id", rng.choice(constants)) if rng.random() < 0.6 else ("num", Fraction(rng.randint(-3, 3)))
            return ("bin", "*", factor, pay_expr(d - 1)) if rng.random() < 0.5 else ("bin", "*", pay_expr(d - 1), factor)
        return ("bin", rng.choice(["+", "-"]), pay_expr(d - 1), pay_expr(d - 1))

    moves = []
    for _ in range(rng.randint(2, 6)):
        who = rng.sample(players, rng.randint(1, len(players)))
        m = Move(rng.choice(["go", "stop", "up", "down", "wait", "left", "right", "pass", "take", "fold"]), who, rng.random() < 0.75,
                 rng.choice(["", "", "", "the %s move" % rng.choice(["first", "last", "odd"]), "a < b & c"]))
        m.end = rng.random() < 0.35
        for _ in range(rng.choice([0, 0, 1, 1, 2])):
            m.conditions.append(bool_expr(rng.randint(0, 2), True))
        if clock:
            m.conditions.append(("bin", "<", ("id", "t"), ("num", Fraction(limit))) if not m.end or rng.random() < 0.3
                                else ("bin", ">=", ("id", "t"), ("num", Fraction(rng.randint(0, limit)))))
        targets = rng.sample(bools + ints + (["ph"] if phases else []), rng.randint(0, len(bools) + len(ints) + bool(phases)))
        for v in targets:
            m.sets.append((v, ("id", rng.choice(phases)) if v == "ph" else
                              bool_expr(1, True) if v in bools else num_expr(1)))
        if clock and not m.end:
            m.sets.append(("t", ("bin", "+", ("id", "t"), ("num", Fraction(1)))))
        rng.shuffle(m.sets)
        for _ in range(rng.choice([0, 1, 1, 2, 3])):
            m.pays.append((rng.choice(players + ["me"] + (["other"] if two else [])), pay_expr(rng.randint(0, 3))))
        if not m.end:
            m.next = ("id", rng.choice(players + ["me"] + (["other"] if two else [])))
        moves.append(m)
    # usually a way to end the game for every player, so that most games end
    if rng.random() < 0.85:
        m = Move("quit", list(players), rng.random() < 0.6, "")
        m.end = True
        moves.append(m)
    rng.shuffle(moves)
    # the compiler takes a name compared with that is never assigned for a misspelling, so compare with assigned ones
    if phases:
        assigned = {state["ph"][1]} | {e[1] for m in moves for v, e in m.sets if v == "ph"}

        def known(e):
            if e[0] == "bin" and e[2] == ("id", "ph") and e[3][1] not in assigned:
                return ("bin", e[1], e[2], state["ph"])
            if e[0] == "bin":
                return ("bin", e[1], known(e[2]), known(e[3]))
            return (e[0], known(e[1])) if e[0] in ("neg", "not") else e
        for m in moves:
            m.conditions = [known(c) for c in m.conditions]
            m.sets = [(v, known(e)) for v, e in m.sets]
    return {"players": players, "constants": constants, "infinitesimals": infinitesimals, "state": state,
            "start": rng.choice(players), "moves": moves, "initial": [c + " > 0" for c in constants if rng.random() < 0.5]}


def write_rules(r, rng):
    """The rules as text, noting the line of each move and clause."""
    lines = ["# random rules"]
    for i, p in enumerate(r["players"]):
        lines.append("players: %s%s" % (p, "  # player %d" % i if rng.random() < 0.3 else ""))
    if r["constants"]:
        lines.append("constants: " + ", ".join(r["constants"]))
    if r["infinitesimals"]:
        lines.append("infinitesimals: " + ", ".join(r["infinitesimals"]))
    lines += ["initial: " + c for c in r["initial"]]
    lines += ["", "start: " + r["start"]]
    r["start_line"] = len(lines)
    if r["state"]:
        lines.append("state: " + ", ".join("%s = %s" % (k, show(v, rng)) for k, v in r["state"].items()))
    for m in r["moves"]:
        lines.append("")
        lines.append("%smove %s by %s%s" % ("honest " if m.honest else "", m.name, ", ".join(m.players),
                                          "  # " + m.description if m.description else ""))
        m.line = len(lines)
        m.condition_lines = []
        for c in m.conditions:
            lines.append("  if " + show(c, rng))
            m.condition_lines.append(len(lines))
        if m.sets:
            lines.append("  set " + ", ".join("%s = %s" % (v, show(e, rng)) for v, e in m.sets))
            m.set_line = len(lines)
        for who, e in m.pays:
            lines.append("  pay %s: %s" % (who, show(e, rng)))
        lines.append("  end" if m.end else "  next " + show(m.next, rng))
        m.next_line = len(lines)
    return "\n".join(lines) + "\n"


# ---- playing the rules out, independently of the compiler ----

def play_out(r, point):
    """The tree the rules give, as checkmate-convert writes it in JSON, and the honest histories; or Expected."""
    players = r["players"]
    leaves = [0]
    honest_histories = []

    def env_of(state, turn):
        env = dict(state)
        env.update({"yes": True, "no": False, "true": True, "false": False, "me": turn})
        env.update({p: p for p in players})
        env.update({p: p for p in ["p0", "p1", "p2"]})
        if len(players) == 2:
            env["other"] = [p for p in players if p != turn][0]
        return env

    def play(turn, state, payoffs, history, line, honest):
        if len(history) >= MAX_DEPTH:
            raise Expected("does not end within", line)
        env = env_of(state, turn)
        possible = [m for m in r["moves"] if turn in m.players and
                    all(value(c, env, line) for c, line in zip(m.conditions, m.condition_lines))]
        if not possible:
            raise Expected("none of their moves is possible", line)
        seen = set()
        for m in possible:
            if m.name in seen:
                raise Expected("two moves %s are possible at once" % m.name, m.line)
            seen.add(m.name)
        if honest and not any(m.honest for m in possible):
            raise Expected("but none of their possible moves", line)
        children = []
        for m in possible:
            new_state = dict(state)
            for v, e in m.sets:
                new_state[v] = value(e, env, m.set_line)
            new_payoffs = list(payoffs)
            for who, e in m.pays:
                i = players.index(env[who] if who in ("me", "other") else who)
                new_payoffs[i] += amount(e, env, point)
            child = {"action": m.name}
            if m.description:
                child["description"] = m.description
            on_honest = honest and m.honest
            if m.end:
                leaves[0] += 1
                if leaves[0] > MAX_COMPARED:
                    raise TooBig()
                child["child"] = {"utility": [{"player": p, "value": new_payoffs[i]} for i, p in enumerate(players)]}
                if on_honest:
                    honest_histories.append(history + [m.name])
            else:
                nxt = value(m.next, env_of(new_state, turn), m.next_line)
                child["child"] = play(nxt, new_state, new_payoffs, history + [m.name], m.line, on_honest)
            children.append(child)
        return {"player": turn, "children": children}

    state = {k: value(e, env_of({}, None), 0) for k, e in r["state"].items()}
    tree = play(r["start"], state, [Fraction(0)] * len(players), [], r["start_line"], True)
    return tree, honest_histories


def evaluate_payoff(text, point):
    """A payoff as the compiler writes it (numbers, names, + - * and parentheses), at `point`."""
    if not re.fullmatch(r"[\w.+\-* ()]*", text):
        raise Bug("unexpected payoff %r" % text)
    code = re.sub(r"\d+(?:\.\d+)?|[A-Za-z_]\w*",
                  lambda m: "Fraction('%s')" % m.group(0) if m.group(0)[0].isdigit() else "V['%s']" % m.group(0), text)
    return eval(code, {"Fraction": Fraction, "V": point})


def compare(expected, actual, point, where="the root"):
    if "utility" in expected:
        if "utility" not in actual:
            raise Bug("at %s: expected a leaf, got %s" % (where, json.dumps(actual)[:200]))
        for e, a in zip(expected["utility"], actual["utility"]):
            if e["player"] != a["player"] or evaluate_payoff(a["value"], point) != e["value"]:
                raise Bug("at %s: the payoff of %s is %s, which is %s, but should be %s" % (
                    where, e["player"], a["value"], evaluate_payoff(a["value"], point), e["value"]))
        if len(expected["utility"]) != len(actual["utility"]):
            raise Bug("at %s: %d payoffs, expected %d" % (where, len(actual["utility"]), len(expected["utility"])))
        return
    if actual.get("player") != expected["player"]:
        raise Bug("at %s: player %s, expected %s" % (where, actual.get("player"), expected["player"]))
    actions = [c["action"] for c in actual.get("children", [])]
    if actions != [c["action"] for c in expected["children"]]:
        raise Bug("at %s: actions %s, expected %s" % (where, actions, [c["action"] for c in expected["children"]]))
    for e, a in zip(expected["children"], actual["children"]):
        if e.get("description") != a.get("description"):
            raise Bug("at %s %s: description %r, expected %r" % (where, e["action"], a.get("description"), e.get("description")))
        compare(e["child"], a["child"], point, e["action"] if where == "the root" else where + " " + e["action"])


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
            ch = rng.choice(" :,=<>()-+*/#\tabmeyno0189") if op == "insert char" else ""
            lines[i] = lines[i][:j] + ch + lines[i][j + (op == "delete char"):]
        if not lines:
            lines = [""]
    return "\n".join(lines)


def fuzz_one(seed, stats):
    rng = random.Random(seed)
    base = unique_file("rulesTest", "")
    files = [base]
    try:
        r = gen_rules(rng)
        text = write_rules(r, rng)
        src, game, game_json = base + ".rules", base + ".game", base + ".json"
        files += [src, game, game_json]
        with open(src, "w") as f:
            f.write(text)
        point = {n: Fraction(rng.randint(-1000, 1000), rng.randint(1, 30)) for n in r["constants"] + r["infinitesimals"]}
        try:
            expected = play_out(r, point)
        except Expected as e:
            expected = e
        except TooBig:
            stats["too big"] = stats.get("too big", 0) + 1
            expected = None
        p = run(["node", args.rules, src, game], check_rc=False) if expected is not None else None
        if p is None:
            pass
        elif p.returncode not in (0, 1) or (p.returncode == 1 and not p.stderr.startswith("rules: ")):
            raise Bug("the compiler crashed (%d):\n%s" % (p.returncode, p.stderr[-3000:]))
        elif isinstance(expected, Expected):
            if p.returncode == 0:
                raise Bug("the rules compile, but should give an error at line %d: ...%s..." % (expected.line, expected.message))
            m = re.match(r"rules: [^:]*: line (\d+): (.*)", p.stderr)
            if not m or int(m.group(1)) != expected.line or expected.message not in m.group(2):
                raise Bug("expected an error at line %d: ...%s..., got: %s" % (expected.line, expected.message, p.stderr.strip()))
            stats["errors"] = stats.get("errors", 0) + 1
        else:
            if p.returncode != 0:
                raise Bug("the rules should compile, but: " + p.stderr.strip())
            run([args.convert, game, game_json])
            actual = json.load(open(game_json))
            tree, honest = expected
            compare(tree, actual["tree"], point)
            if actual["honest_histories"] != honest:
                raise Bug("honest histories %s, expected %s" % (actual["honest_histories"], honest))
            stats["compiled"] = stats.get("compiled", 0) + 1
            if rng.random() < args.analyse:
                try:
                    run([args.checkmate, game], timeout=args.tout)
                    stats["analysed"] = stats.get("analysed", 0) + 1
                except subprocess.TimeoutExpired:
                    stats["analysis timeouts"] = stats.get("analysis timeouts", 0) + 1

        for k in range(3):
            m = base + "-mutated%d.rules" % k
            files.append(m)
            with open(m, "w") as f:
                f.write(mutate(rng, text))
            p = run(["node", args.rules, m], check_rc=False)
            if p.returncode not in (0, 1) or (p.returncode == 1 and not p.stderr.startswith("rules: ")):
                raise Bug("the compiler crashed (%d) on the mutated %s:\n%s" % (p.returncode, m, p.stderr[-3000:]))
            key = "mutants rejected" if p.returncode else "mutants accepted"
            stats[key] = stats.get(key, 0) + 1
    except Bug as e:
        print("=" * 60)
        print("BUG: %s" % e)
        print("files: %s" % " ".join(f for f in files if os.path.exists(f)))
        print("REPRODUCE with: scripts/fuzz_rules.py --seed %d --num 1" % seed)
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
    ap.add_argument("--analyse", type=float, default=0.1, help="share of compiled games that checkmate analyses")
    ap.add_argument("--rules", default=os.path.join(SCRIPTS, "rules.mjs"))
    ap.add_argument("--checkmate", default="build/checkmate")
    ap.add_argument("--convert", default="build/checkmate-convert")
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
