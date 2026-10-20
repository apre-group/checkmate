# Split a game into a subtree and a supertree for compositional (--subtree) fuzzing.

import copy


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
