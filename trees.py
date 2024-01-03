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
        self.honest = False
        for branch in self.actions:
            branch.tree.reset_honest()

    def reset_strategy(self):
        self.reason = None
        self.strategy = 0
        for branch in self.actions:
            branch.tree.reset_strategy()

    def weak_immune(self, solver: z3.Solver, player: str, weaker: bool) -> bool:
        if player == self.player:
            if self.honest:
                self.strategy = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                if self.actions[self.strategy].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                return False

            while self.strategy < len(self.actions):
                if self.actions[self.strategy].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                self.strategy += 1

            return False

        for action in self.actions:
            if not action.tree.weak_immune(solver, player, weaker):
                self.reason = action.tree.reason
                return False

        return True

    def collusion_resilient(self, solver: z3.Solver, group: set[str], honest: Utility) -> bool:
        if self.player not in group:
            if self.honest:
                self.strategy = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                if self.actions[self.strategy].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                return False

            while self.strategy < len(self.actions):
                if self.actions[self.strategy].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.strategy].tree.reason is not None:
                    self.reason = self.actions[self.strategy].tree.reason
                self.strategy += 1
            return False

        for action in self.actions:
            if not action.tree.collusion_resilient(solver, group, honest):
                self.reason = action.tree.reason
                return False

        return True

    def practical(self, solver: z3.Solver, players: list[str]) -> Optional[dict[str, Utility]]:
        players = [self.player] + [
            player for player in players
            if player != self.player
        ]
        utilities = []
        for action in self.actions:
            utility = action.tree.practical(solver, players)
            if utility is None:
                self.reason = action.tree.reason
                return None
            utilities.append(utility)

        if self.honest:
            self.strategy = next(
                index for index in
                range(len(self.actions))
                if self.actions[index].tree.honest
            )
            maximum = utilities[self.strategy][self.player]
            for utility in utilities:
                if solver.check(not_(maximum >= utility[self.player])) != z3.unsat:
                    if solver.check(not_(maximum < utility[self.player])) != z3.unsat:
                        self.reason = maximum, utility[self.player]
                    return None

        def find_maxima(utilities: list[dict[str, Utility]], player: str) -> Optional[list[dict[str, Utility]]]:
            maxima = []
            for utility in utilities:
                if any(
                    solver.check(not_(maximum[player] > utility[player])) == z3.unsat
                    for maximum in maxima
                ):
                    continue
                maxima = [
                    maximum
                    for maximum in maxima
                    if solver.check(
                        not_(utility[player] > maximum[player])
                    ) != z3.unsat
               ]
                maxima.append(utility)

            for i in range(0, len(maxima) - 1):
                lhs = maxima[i][player]
                rhs = maxima[i + 1][player]
                if solver.check(not_(lhs == rhs)) != z3.unsat:
                    self.reason = lhs, rhs
                    return None

            return maxima

        maxima = utilities
        for player in players:
            next_maxima = []
            for utility in maxima:
                if any(
                    solver.check(not_(maximum[player] > utility[player])) == z3.unsat
                    for maximum in next_maxima
                ):
                    continue
                next_maxima = [
                    maximum
                    for maximum in next_maxima
                    if solver.check(
                        not_(utility[player] > maximum[player])
                    ) != z3.unsat
                ]
                next_maxima.append(utility)

            for i in range(0, len(next_maxima) - 1):
                lhs = next_maxima[i][player]
                rhs = next_maxima[i + 1][player]
                if solver.check(not_(lhs == rhs)) != z3.unsat:
                    self.reason = lhs, rhs
                    return None

            maxima = next_maxima

        result = maxima[0]
        self.strategy = next(
            index for index in range(len(utilities))
            if id(utilities[index]) == id(result)
        )
        return result
