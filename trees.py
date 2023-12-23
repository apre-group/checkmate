from typing import Iterable, Optional
import z3

from auxfunz3 import Boolean, not_
from utility import Utility

class Tree:
    """base class for game trees"""
    honest: bool
    """if this node is along the honest history"""
    reason: Optional[Boolean]

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
        self.reason = False

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

        self.reason = condition
        return False

    def collusion_resilient(self, solver: z3.Solver, group: set[str], honest: Utility) -> bool:
        group_utility = sum(self.utilities[player] for player in group)
        condition = group_utility <= honest
        if solver.check(not_(condition)) == z3.unsat:
            return True
        elif solver.check(condition) == z3.unsat:
            return False

        self.reason = condition
        return False

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
    """the current player"""
    actions: list[Action]
    """available actions leading to sub-trees"""
    current: int
    """the current action for the strategy"""

    def __init__(self, player: str, actions: dict[str, Tree]):
        super().__init__()
        self.player = player
        self.actions = [Action(action, tree) for action, tree in actions.items()]
        self.current = 0

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
        self.current = 0
        for branch in self.actions:
            branch.tree.reset_strategy()

    def weak_immune(self, solver: z3.Solver, player: str, weaker: bool) -> bool:
        if player == self.player:
            if self.honest:
                self.current = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                if self.actions[self.current].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.current].tree.reason is not None:
                    self.reason = self.actions[self.current].tree.reason
                return False

            while self.current < len(self.actions):
                if self.actions[self.current].tree.weak_immune(solver, player, weaker):
                    return True
                if self.actions[self.current].tree.reason is not None:
                    self.reason = self.actions[self.current].tree.reason
                self.current += 1

            return False

        for action in self.actions:
            if not action.tree.weak_immune(solver, player, weaker):
                self.reason = action.tree.reason
                return False

        return True

    def collusion_resilient(self, solver: z3.Solver, group: set[str], honest: Utility) -> bool:
        if self.player not in group:
            if self.honest:
                self.current = next(
                    index for index in
                    range(len(self.actions))
                    if self.actions[index].tree.honest
                )
                if self.actions[self.current].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.current].tree.reason is not None:
                    self.reason = self.actions[self.current].tree.reason
                return False

            while self.current < len(self.actions):
                if self.actions[self.current].tree.collusion_resilient(solver, group, honest):
                    return True
                if self.actions[self.current].tree.reason is not None:
                    self.reason = self.actions[self.current].tree.reason
                self.current += 1
            return False

        for action in self.actions:
            if not action.tree.collusion_resilient(solver, group, honest):
                self.reason = action.tree.reason
                return False

        return True
