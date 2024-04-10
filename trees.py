from typing import Iterable, Optional
import z3

from auxfunz3 import not_, Boolean
from utility import Utility

class Utilities:
    """map from players to their utilities"""
    utilities: dict[str, Utility]
    """underlying map"""

    def __init__(self, utilities: dict[str, Utility]):
        self.utilities = utilities

    def __getitem__(self, key: str) -> Utility:
        return self.utilities[key]

    def __hash__(self) -> int:
        return hash((
            utility
            for utility in self.utilities.values()
        ))

    def __eq__(self, other: 'Utilities') -> bool:
        return all(
            l.eq(r)
            for l, r in zip(self.utilities.values(), other.utilities.values())
        )

    def __repr__(self):
        return repr(self.utilities)

    def items(self):
        return self.utilities.items()

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

    def practical(self, *_) -> set[Utilities]:
        assert False

class Leaf(Tree):
    """a leaf node"""
    utilities: Utilities
    """player utilities"""

    def __init__(self, utilities: Utilities):
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

    def mark_honest(self, honest_history: list[str]) -> Utilities:
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

        self.reason = utility >= 0
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

    def practical(self, *_) -> set[Utilities]:
        return {self.utilities}


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

        if player == self.player: # player behaves honestly
            if self.honest:
                # if we are along honest history, we must take the honest strategy
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

        # if we are not the honest player, we could do anything,
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

        if self.player not in group: # player follows honest history
            if self.honest:
                # if we are along honest history, we must take the honest strategy
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
            # NB we leave `self.strategy` where it is from previous colluding groups --> to be considered in soundness proof
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

    def practical(self, solver: z3.Solver) -> set[Utilities]:
        """
        check if this tree is practical

        returns leaf utilities for the resulting strategy if practical
        returns empty set if not practical, setting `self.reason` if a case-split is required
        """

        # get practical strategies and corresponding utilities recursively
        children = []
        for action in self.actions:
            utilities = action.tree.practical(solver)
            # there is no practical child (propagate reason for case split, if any)
            if not utilities:
                self.reason = action.tree.reason
                return set()
            children.append(utilities)

        if self.honest:
            # if we are at an honest node, our strategy must be the honest strategy
            self.strategy = next(
                index for index in
                range(len(self.actions))
                if self.actions[index].tree.honest
            )

            honest_utilities = children.pop(self.strategy)
            assert len(honest_utilities)==1
            # the utility at the leaf of the honest history
            honest_utility = honest_utilities.pop()
            # this should be maximal against other children, so...
            maximum = honest_utility[self.player]

            # for all the other children:
            for utilities in children:
                found = False
                # does there exist a possible utility such that `maximum` is geq than it?
                for utility in utilities:
                    if solver.check(maximum < utility[self.player]) == z3.sat:
                        if solver.check(maximum >= utility[self.player]) == z3.sat:
                            # might be maximal, just couldn't prove it
                            self.reason = maximum >= utility[self.player]
                    else:
                        found = True
                        break
                if not found:
                    return set()

            # and we return the maximal strategy
            # honest choice is practical for current player
            return {honest_utility}
        else:
            # not in the honest history
            # TODO this could be done more efficiently by working out the set of utilities for `self.player`
            # but utilities can't be put in a set easily: fix this in the C++ version

            # compute the set of possible utilities by merging children's utilities
            result = set(
                utility
                for utilities in children
                for utility in utilities
            )
            # the set to drop
            remove = set()

            # work out whether to drop `candidate`
            for candidate in result:
                # this player's utility
                dominatee = candidate[self.player]

                # check all the other children
                # if any child has the property that all its utilitites are bigger than `dominatee`,
                # it can be dropped
                for utilities in children:
                    # skip any where the candidate is already contained
                    if any(utility is candidate for utility in utilities):
                        continue

                    # *all* utilities have to be bigger
                    dominated = True
                    for utility in utilities:
                        dominator = utility[self.player]
                        if solver.check(dominator <= dominatee) == z3.sat:
                            dominated = False
                            if solver.check(dominator > dominatee) == z3.sat:
                                # might be dominanated, but can't prove it
                                self.reason = dominator > dominatee
                                return set()

                    if dominated:
                        remove.add(candidate)
                        break

            # result is all children's utilities inductively, minus those dropped
            return result - remove
