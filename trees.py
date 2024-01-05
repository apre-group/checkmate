from typing import Iterable, Optional, Union
import z3

from auxfunz3 import Real, not_
from utility import Utility

class Tree:
    """base class for game trees"""
    honest: bool
    """if this node is along the honest history"""
    reason: Optional[tuple[Union[Real, Utility], Union[Real, Utility]]]

    def __init__(self):
        self.honest = False
        self.reason = None

    def reset_honest(self):
        assert False

    def reset_strategy(self):
        assert False

    def mark_honest(self, *_) -> dict[str, Utility]:
        assert False

    def weak_immune(self, *_) -> bool:
        assert False

    def collusion_resilient(self, *_) -> bool:
        assert False

    def practical(self, *_) -> Optional[dict[str, Utility]]:
        assert False

class Leaf(Tree):
    """a leaf node"""
    utilities: dict[str, Utility]
    """player utilities"""

    def __init__(self, utilities: dict[str, Utility]):
        super().__init__()
        self.utilities = utilities

    def __repr__(self) -> str:
        return '\n'.join(
            f"{player}: {utility}"
            for player, utility in self.utilities.items()
        )

    def reset_honest(self):
        self.honest = False

    def reset_strategy(self):
        self.reason = None

    def mark_honest(self, honest_history: list[str]) -> dict[str, Utility]:
        """mark this branch as honest"""
        self.honest = True
        assert not honest_history
        return self.utilities

    def weak_immune(self, solver: z3.Solver, player: str, weaker: bool):
        utility = self.utilities[player]
        if weaker:
            utility = utility.real
        condition = utility >= 0
        if solver.check(not_(condition)) == z3.unsat:
            return True
        elif solver.check(condition) == z3.unsat:
            return False

        self.reason = utility, 0
        return False

    def collusion_resilient(self, solver: z3.Solver, group: set[str], honest: Utility) -> bool:
        group_utility = sum(self.utilities[player] for player in group)
        condition = group_utility <= honest
        if solver.check(not_(condition)) == z3.unsat:
            return True
        elif solver.check(condition) == z3.unsat:
            return False

        self.reason = group_utility, honest
        return False

    def practical(self, *_) -> Optional[dict[str, Utility]]:
        return self.utilities


class Action:
    name: str
    """the action name"""
    tree: Tree
    """the sub-tree from this action"""

    def __init__(self, name: str, tree: Tree):
        self.name = name
        self.tree = tree

class Branch(Tree):
    """a non-leaf node with children"""
    player: str
    """the player at this node"""
    actions: list[Action]
    """available actions leading to sub-trees"""
    strategy: int
    """the action index to take for the strategy"""

    def __init__(self, player: str, actions: dict[str, Tree]):
        super().__init__()
        self.player = player
        self.actions = [Action(action, tree) for action, tree in actions.items()]
        self.strategy = 0

    def __repr__(self) -> str:
        # magic for pretty trees
        def pad(x: Iterable[str]) -> str:
            return '\n'.join(f"| {line}" for line in x)

        actions = '\n'.join(
            f"`>{action.name}\n{pad(repr(action.tree).splitlines())}"
            for action in self.actions
        )
        return f"{self.player}\n{actions}"

    def mark_honest(self, honest_history: list[str]) -> dict[str, Utility]:
        """mark this branch as honest"""
        assert honest_history
        self.honest = True
        index = [action.name for action in self.actions].index(honest_history[0])
        return self.actions[index].tree.mark_honest(honest_history[1:])

    def reset_honest(self):
        """reset all the honest flags"""
        self.honest = False
        for branch in self.actions:
            branch.tree.reset_honest()

    def reset_strategy(self):
        """reset all the strategy/reason flags"""
        self.reason = None
        self.strategy = 0
        for branch in self.actions:
            branch.tree.reset_strategy()

    def weak_immune(self, solver: z3.Solver, player: str, weaker: bool) -> bool:
        """
        check if this tree is weak(er) immune for `player`
        returns false if a case-split is required and sets `self.reason`
        """

        if player == self.player:
            if self.honest:
                # if we are honest, we must take the honest strategy
                self.strategy = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                # the honest choice must be weak immune
                if self.actions[self.strategy].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                return False

            # otherwise, we can take any strategy we please as long as it's weak immune
            while self.strategy < len(self.actions):
                if self.actions[self.strategy].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                self.strategy += 1

            return False

        # if we are not the player, we could do anything,
        # so all branches should be weak immune for the player
        for action in self.actions:
            if not action.tree.weak_immune(solver, player, weaker):
                self.reason = action.tree.reason
                return False

        return True

    def collusion_resilient(self, solver: z3.Solver, group: set[str], honest: Utility) -> bool:
        """
        check if this tree is collusion-resilient against `group`
        returns false if a case-split is required and sets `self.reason`
        """

        if self.player not in group:
            if self.honest:
                # if we are honest, we must take the honest strategy
                self.strategy = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                # the honest choice must be collusion resilient
                if self.actions[self.strategy].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                return False

            # otherwise, we can take any strategy we please as long as it's collusion resilient
            # NB we leave `self.strategy` where it is from previous colluding groups
            while self.strategy < len(self.actions):
                if self.actions[self.strategy].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                self.strategy += 1
            return False

        # if we are in the colluding group, we could do anything,
        # so all branches should be resilient against us
        for action in self.actions:
            if not action.tree.collusion_resilient(solver, group, honest):
                self.reason = action.tree.reason
                return False

        return True

    def practical(self, solver: z3.Solver, players: list[str]) -> Optional[dict[str, Utility]]:
        """
        check if this tree is practical

        returns leaf utilities for the resulting strategy if practical
        returns None if not practical, setting `self.reason` if a case-split is required

        `players` is a list of players upwards from here, used for tie-breaking equal utilities
        """

        # maintain a de-duplicated list of players upwards from this node
        players = [self.player] + [
            player for player in players
            if player != self.player
        ]

        # get practical strategies and corresponding utilities recursively
        utilities = []
        for action in self.actions:
            utility = action.tree.practical(solver, players)
            # child is not practical
            if utility is None:
                self.reason = action.tree.reason
                return None
            utilities.append(utility)

        if self.honest:
            # if we are at an honest node, our strategy must be the honest strategy
            self.strategy = next(
                index for index in
                range(len(self.actions))
                if self.actions[index].tree.honest
            )
            # which means the corresponding utility should be maximal
            maximum = utilities[self.strategy][self.player]
            for utility in utilities:
                if solver.check(maximum < utility[self.player]) == z3.sat:
                    if solver.check(maximum >= utility[self.player]) == z3.sat:
                        # might be maximal, just couldn't prove it
                        self.reason = maximum, utility[self.player]
                    return None
            # and we return the maximal strategy
            return utilities[self.strategy]

        # otherwise, we must find the maximal utility available to us
        # if there two actions with the same utility:
        # 1. we tie-break by considering the preference of players above us
        # 2. we *must* do this, otherwise we might miss a practical strategy
        # consider e.g. player A has an honest choice, and a dishonest choice with utility 0
        # in the honest branch, player B has two choices with utility 0 for B
        # but for player A, they have utilities 0 and -epsilon
        # B must choose (0, 0) not (0, -epsilon) for a practical strategy

        # current maxima are all utilities
        maxima = utilities
        # for each player, starting with us
        for player in players:
            # the next set of maximal utilities, which will be a subset of `maxima`
            next_maxima = []
            for utility in maxima:
                # if any other utility is larger, `utility` is not a maximum
                if any(
                    solver.check(maximum[player] <= utility[player]) == z3.unsat
                    for maximum in next_maxima
                ):
                    continue

                # retain only candidate maxima not less than `utility`
                next_maxima = [
                    maximum
                    for maximum in next_maxima
                    if solver.check(utility[player] <= maximum[player]) == z3.sat
                ]
                next_maxima.append(utility)

            # all maxima should be equal - otherwise we need to case-split
            for i in range(0, len(next_maxima) - 1):
                lhs = next_maxima[i][player]
                rhs = next_maxima[i + 1][player]
                if solver.check(lhs != rhs) == z3.sat:
                    self.reason = lhs, rhs
                    return None

            maxima = next_maxima

        # if *nobody* cares, we can just take the first one
        result = maxima[0]
        self.strategy = next(
            index for index in range(len(utilities))
            if id(utilities[index]) == id(result)
        )
        return result
