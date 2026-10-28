# Split a game into a subtree and a supertree for compositional (--subtree) fuzzing.

import copy

from gen_cefg import declare, declared, edges, follow_honest, honest_utility, revealed_at, truncate_honest
from gen_cefg import node_at as cefg_node_at


def branches(tree, hist=()):
    if "children" in tree:
        yield hist, tree
        for c in tree["children"]:
            yield from branches(c["child"], hist + (c["action"],))


def node_at(tree, hist):
    for a in hist:
        tree = next(c["child"] for c in tree["children"] if c["action"] == a)
    return tree


def split(game, rng):
    """Cut below a random non-root branch of a game with one honest history or one honest utility.
    Returns (subtree game, cut history) or None."""
    candidates = [(h, n) for h, n in branches(game["tree"]) if h]
    if not candidates:
        return None
    hist, node = rng.choice(candidates)
    sub = {k: copy.deepcopy(v) for k, v in game.items() if k not in ("tree", "honest_histories", "honest_utilities")}
    sub["tree"] = copy.deepcopy(node)
    honest = game["honest_histories"][0] if game["honest_histories"] else None
    if honest is not None and tuple(honest[:len(hist)]) == hist:
        sub["honest_histories"] = [list(honest[len(hist):])]
    else:
        sub["honest_histories"] = []
        sub["honest_utilities"] = (copy.deepcopy(game["honest_utilities"]) if honest is None
                                   else [{"utility": copy.deepcopy(node_at(game["tree"], honest)["utility"])}])
    return sub, hist


def splice(game, hist, subtree_result):
    g = copy.deepcopy(game)
    parent = node_at(g["tree"], hist[:-1])
    for c in parent["children"]:
        if c["action"] == hist[-1]:
            c["child"] = subtree_result
    return g


def cefg_split(game, rng):
    """Cut below a random node other than the root (a branch or condition node) of a CEFG with one honest history
    or one honest utility. Returns (subtree game, steps to the cut, whether the cut is along the honest history) or None.
    Constants revealed on the way to the cut are known in the subtree."""
    candidates = []

    def walk(node, steps, revealed):
        if steps and ("children" in node or "condition" in node):
            candidates.append((steps, node, revealed))
        below = revealed | revealed_at(node, unknown) if "condition" in node else revealed
        for step, c in edges(node):
            walk(c, steps + [step], below)
    known, unknown = declared(game["constants"])
    walk(game["tree"], [], frozenset())
    if not candidates:
        return None
    steps, node, revealed = rng.choice(candidates)
    sub = {k: copy.deepcopy(v) for k, v in game.items() if k not in ("tree", "honest_histories", "honest_utilities")}
    sub["constants"] = declare(known + [u for u in unknown if u in revealed], [u for u in unknown if u not in revealed])
    sub["tree"] = copy.deepcopy(node)
    honest = game["honest_histories"][0] if game["honest_histories"] else None
    rest = follow_honest(game["tree"], honest, steps) if honest is not None else None
    if rest is not None:
        sub["honest_histories"] = [rest]
        sub["honest_utilities"] = []
    else:
        sub["honest_histories"] = []
        sub["honest_utilities"] = (copy.deepcopy(game["honest_utilities"]) if honest is None
                                   else [{"utility": honest_utility(game["tree"], honest)}])
    return sub, steps, rest is not None


def cefg_splice(game, steps, subtree_result, along):
    """`game` with the node at `steps` replaced by the subtree results (SUBTREE.out: the subtree node of an EFG, the list
    of entries of a CEFG); along the honest history, the honest history ends there."""
    g = copy.deepcopy(game)
    parent = cefg_node_at(g["tree"], steps[:-1])
    kind, s = steps[-1]
    node = subtree_result if isinstance(subtree_result, dict) else {"subtree": subtree_result}
    if kind == "a":
        next(c for c in parent["children"] if c["action"] == s)["child"] = node
    else:
        parent["condition"][s]["child"] = node
    if along:
        g["honest_histories"] = [truncate_honest(game["tree"], game["honest_histories"][0], steps)]
    return g
