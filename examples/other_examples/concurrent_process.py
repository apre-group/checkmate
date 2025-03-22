from dsl import *

current, savings, transfer = CONSTANTS = constants('current', 'savings', 'transfer')
total = current + savings
p1, p2, customer, agency = PLAYERS = players('p1', 'p2', 'customer', 'agency')
go, no = ACTIONS = actions('go', 'no')


def mk_leaf(reported):
    return leaf({
        p1: 0,
        p2: 0,
        customer: reported - total,
        agency: total - reported
    })


def tree(
    player = p1,
    s1 = 'a', s2 = 'a',
    c = current, s = savings, reported = 0,
    just_paused = False
):
    if s1 == 'done' and s2 == 'done':
        return mk_leaf(reported)

    if player == p1:
        if s1 == 'a':
            actions = {go: tree(p2, 'b', s2, c, s, reported + c, False)}
            if not just_paused and s2 != 'done':
                actions[no] = tree(p2, 'a', s2, c, s, reported, True)
            return branch(p1, actions)
        elif s1 == 'b':
            actions = {go: tree(p2, 'done', s2, c, s, reported + s, False)}
            if not just_paused and s2 != 'done':
                actions[no] = tree(p2, s1, s2, c, s, reported, True)
            return branch(p1, actions)
        else:
            return tree(p2, s1, s2, c, s, reported, True)
    else:
        if s2 == 'a':
            actions = {go: tree(p1, s1, 'b', c - transfer, s, reported, False)}
            if not just_paused and s1 != 'done':
                actions[no] = tree(p1, s1, s2, c, s, reported, True)
            return branch(p2, actions)
        elif s2 == 'b':
            actions = {go: tree(p1, s1, 'done', c, s + transfer, reported, False)}
            if not just_paused and s1 != 'done':
                actions[no] = tree(p1, s1, s2, c, s, reported, True)
            return branch(p2, actions)
        else:
            return tree(p1, s1, s2, c, s, reported, True)


finish(
    PLAYERS,
    ACTIONS,
    [],
    CONSTANTS,
    [current > 0, savings > 0, transfer > 0, current - transfer > 0],
    [],
    [],
    [],
    [],
    [
        [go, go, go, go]
    ],
    tree()
)

