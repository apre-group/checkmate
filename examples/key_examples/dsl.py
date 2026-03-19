from __future__ import annotations
import json
from typing import Dict, Union, List


class StringThing:
    value: str

    def __init__(self, value: str):
        self.value = value

    def __repr__(self):
        return self.value

    def __str__(self):
        return self.value

    def json(self):
        return repr(self)


class Action(StringThing):
    pass


class Player(StringThing):
    pass


class Expr:
    def __add__(self, other: LExpr) -> LExpr:
        return add_expr(self, other)

    def __radd__(self, other: LExpr) -> LExpr:
        return add_expr(other, self)

    def __sub__(self, other: LExpr) -> LExpr:
        return sub_expr(self, other)

    def __rsub__(self, other: LExpr) -> LExpr:
        return sub_expr(other, self)

    def __mul__(self, other: LExpr) -> LExpr:
        return mul_expr(self, other)

    def __rmul__(self, other: LExpr) -> LExpr:
        return mul_expr(other, self)

    def __truediv__(self, other: LExpr) -> LExpr:
        return div_expr(other, self)

    def __rtruediv__(self, other: LExpr) -> LExpr:
        return div_expr(other, self)

    def __neg__(self) -> TermExpr:
        return neg_expr(self)

    def __ne__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('!=', self, other)

    def __gt__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('>', self, other)

    def __ge__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('>=', self, other)

    def __lt__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('<', self, other)

    def __le__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('<=', self, other)

    def __eq__(self, other: LExpr) -> Constraint:
        return DisequationConstraint('=', self, other)


    def json(self):
        return repr(self)


class NameExpr(Expr):
    name: str

    def __init__(self, name: str):
        self.name = name

    def __repr__(self):
        return self.name

    def __hash__(self) -> int:
        return self.name.__hash__()


LExpr = Union[Expr, float, int]


def is_exactly(expr: LExpr, value: float) -> bool:
    return (isinstance(expr, float) or isinstance(expr, int)) and expr == value


class TermExpr(Expr):
    constant: float
    coefficients: Dict[Expr, float]

    def __init__(self, constant: float, coefficients: Dict[Expr, float]):
        self.constant = constant
        self.coefficients = coefficients

    @staticmethod
    def from_expr(expr: LExpr) -> TermExpr:
        if isinstance(expr, TermExpr):
            return expr
        elif isinstance(expr, float) or isinstance(expr, int):
            return TermExpr(float(expr), {})

        return TermExpr(0.0, {expr: 1})

    @staticmethod
    def negate(expr: TermExpr) -> TermExpr:
        constant = -expr.constant
        coefficients = {
            key: -value
            for key, value in expr.coefficients.items()
        }
        return TermExpr(constant, coefficients)

    @staticmethod
    def add(left: TermExpr, right: TermExpr) -> TermExpr:
        constant = left.constant + right.constant
        coefficients = dict(left.coefficients)
        for key, value in right.coefficients.items():
            if key in coefficients:
                coefficients[key] += value
                if coefficients[key] == 0.0:
                    del coefficients[key]
            else:
                coefficients[key] = value

        return TermExpr(constant, coefficients)

    @staticmethod
    def sub(left: TermExpr, right: TermExpr) -> TermExpr:
        return TermExpr.add(left, TermExpr.negate(right))

    @staticmethod
    def mul_constant(expr: TermExpr, factor: float) -> TermExpr:
        constant = factor * expr.constant
        coefficients = {
            key: factor * value
            for key, value in expr.coefficients.items()
        }
        return TermExpr(constant, coefficients)

    def __repr__(self):
        if not self.coefficients:
            return str(self.constant)

        positive = {
            key: value
            for key, value in self.coefficients.items()
            if value > 0.0
        }
        negative = {
            key: abs(value)
            for key, value in self.coefficients.items()
            if value < 0.0
        }

        result = str(self.constant) if self.constant > 0.0 else ''
        need_join = self.constant > 0.0

        for key, value in positive.items():
            factor = '' if value == 1.0 else f'{value} * '
            join = ' + ' if need_join else ''
            need_join = True
            result += f'{join}{factor}{key}'

        for key, value in negative.items():
            factor = '' if value == 1.0 else f'{value} * '
            join = ' - ' if need_join else '-'
            need_join = True
            result += f'{join}{factor}{key}'

        if self.constant < 0.0:
            result += f" - {abs(self.constant)}"

        return result


def neg_expr(expr: LExpr) -> TermExpr:
    return TermExpr.negate(TermExpr.from_expr(expr))


def add_expr(left: LExpr, right: LExpr) -> LExpr:
    if is_exactly(left, 0.0):
        return right
    elif is_exactly(right, 0.0):
        return left

    left = TermExpr.from_expr(left)
    right = TermExpr.from_expr(right)
    return TermExpr.add(left, right)


def sub_expr(left: LExpr, right: LExpr) -> LExpr:
    if is_exactly(right, 0.0):
        return left

    left = TermExpr.from_expr(left)
    right = TermExpr.from_expr(right)
    return TermExpr.sub(left, right)


class MultiplicationExpr(Expr):
    left: LExpr
    right: LExpr

    def __init__(self, left: LExpr, right: LExpr):
        self.left = left
        self.right = right

    def __repr__(self):
        left = f"({self.left})" if isinstance(self.left, TermExpr) else f"{self.left}"
        right = f"({self.right})" if isinstance(self.right, TermExpr) else f"{self.right}"
        return f"{left} * {right}"

    def __hash__(self) -> int:
        return f"{self.left} * {self.right}".__hash__()


def mul_expr(left: LExpr, right: LExpr) -> LExpr:
    if is_exactly(left, 0.0) or is_exactly(right, 0.0):
        return 0.0
    elif is_exactly(left, 1.0):
        return right
    elif is_exactly(right, 1.0):
        return left
    elif isinstance(left, int) or isinstance(left, float):
        right = TermExpr.from_expr(right)
        return TermExpr.mul_constant(right, float(left))
    elif isinstance(right, int) or isinstance(right, float):
        left = TermExpr.from_expr(left)
        return TermExpr.mul_constant(left, float(right))

    return MultiplicationExpr(left, right)


class DivisionExpr(Expr):
    left: LExpr
    right: LExpr

    def __init__(self, left: LExpr, right: LExpr):
        self.left = left
        self.right = right

    def __repr__(self):
        left = f"({self.left})" if isinstance(self.left, TermExpr) else f"{self.left}"
        right = f"({self.right})" if isinstance(self.right, TermExpr) else f"{self.right}"
        return f"{left} / {right}"

    def __hash__(self) -> int:
        return f"{self.left} * {self.right}".__hash__()


def div_expr(left: LExpr, right: LExpr) -> LExpr:
    if is_exactly(right, 0.0) or (isinstance(right, int) and is_exactly(right, 0)):
        raise ZeroDivisionError
    if is_exactly(left, 0.0) or (isinstance(left, int) and is_exactly(left, 0)):
        return 0.0
    elif is_exactly(right, 1.0) or (isinstance(right, int) and is_exactly(right, 1)):
        return left

    return DivisionExpr(left, right)


class Constraint:
    def json(self):
        return repr(self)

class Truth(Constraint):

    def __init__(self) -> None:
        pass

    def __repr__(self) -> str:
        return "True"

class Falsehood(Constraint):

    def __init__(self) -> None:
        pass

    def __repr__(self) -> str:
        return "False"


class DisequationConstraint(Constraint):
    op: str
    left: LExpr
    right: LExpr

    def __init__(self, op: str, left: LExpr, right: LExpr):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return f"{self.left} {self.op} {self.right}"


class Conjunction(Constraint):
    args: List[Constraint]

    def __init__(self, args: List[Constraint]):
        self.args = args

    def __repr__(self):
        result = f""
        for elem in self.args:
            result = result + f" & {elem}"
        result = result[3:]
        return result

def conjunction(*args) -> Conjunction:
    arg_list = []
    for elem in args:
        arg_list.append(elem)
    return Conjunction(arg_list)


class Disjunction(Constraint):
    args: List[Constraint]

    def __init__(self, args: List[Constraint]):
        self.args = args

    def __repr__(self):
        result = f""
        for elem in self.args:
            result = result + f" | {elem}"
        result = result[3:]
        return result

def disjunction(*args) -> Disjunction:
    arg_list = []
    for elem in args:
        arg_list.append(elem)
    return Disjunction(arg_list)



class HistoryTree:

    def __init__(self, path: List[Union[Action, List['HistoryTreeCondition']]]):
        self.path = path

    def json(self):
        return [
            ch.json() if isinstance(ch, HistoryTreeCondition) else repr(ch)
            for ch in self.path
        ]

class HistoryTreeCondition(HistoryTree):
    def __init__(self, condition: Constraint, path: HistoryTree):
        self.condition = condition
        self.path = path

    def json(self):
        return {
            'condition': self.condition.json(),
            'path': self.path.json()
        }

class HonestUtility:
    """Represents honest utility - either a simple utility mapping or conditional utilities"""
    
    def __init__(self, utility: Union[Dict[Player, LExpr], List['HonestUtilityCondition']]):
        self.utility = utility

    def json(self):
        if isinstance(self.utility, dict):
            # Simple utility mapping
            return {
                'utility': [
                    {'player': player, 'value': utility}
                    for player, utility in self.utility.items()
                ]
            }
        else:
            # Conditional utilities
            return {
                'utility': [cond.json() for cond in self.utility]
            }
        
    def graphviz(self):
        if isinstance(self.utility, dict):
            print(f'\tn{id(self)} [label="HonestUtility"];')
            for player, utility in self.utilities.items():
                print(f'\tn{id(self)}_{player} [label="{utility}"];')
                print(f'\tn{id(self)} -> n{id(self)}_{player} [label="{player}"];')
            
        else:
            print(f'\tn{id(self)} [label="HonestUtility"];')
            for cond in self.utility:
                cond.graphviz()
                print(f'\tn{id(self)} -> n{id(cond)};')


class HonestUtilityCondition:
    """Represents a conditional branch in honest utility"""
    
    def __init__(self, condition: Constraint, utility: Union[Dict[Player, LExpr], List['HonestUtilityCondition']]):
        self.condition = condition
        self.utility = utility
    
    def json(self):
        if isinstance(self.utility, dict):
            # Simple utility mapping
            return {
                'condition': self.condition.json(),
                'utility': [
                    {'player': player, 'value': utility_val}
                    for player, utility_val in self.utility.items()
                ]
            }
        else:
            # Nested conditional utilities
            return {
                'condition': self.condition.json(),
                'utility': [cond.json() for cond in self.utility]
            }
        
    def graphviz(self):
        print(f'\tn{id(self)} [label="*"];')
        print(f'\tn{id(self)} -> n{id(self.condition)} [label="condition"];')
        self.condition.graphviz()
        
        if isinstance(self.utility, dict):
            for player, utility in self.utility.items():
                print(f'\tn{id(self)}_{player} [label="{utility}"];')
                print(f'\tn{id(self)} -> n{id(self)}_{player} [label="{player}"];')
        else:
            for cond in self.utility:
                cond.graphviz()
                print(f'\tn{id(self)} -> n{id(cond)};')

class Tree:
    def graphviz(self):
        raise NotImplementedError()


class Leaf(Tree):
    def __init__(self, utilities: Dict[Player, LExpr]):
        self.utilities = utilities

    def json(self):
        return {
            'utility': [
                {'player': player, 'value': utility}
                for player, utility in self.utilities.items()
            ]
        }

    def graphviz(self):
        print(f'\tn{id(self)} [label="*"];')
        for player, utility in self.utilities.items():
            print(f'\tn{id(self)}_{player} [label="{utility}"];')
            print(f'\tn{id(self)} -> n{id(self)}_{player} [label="{player}"];')


def leaf(utilities: Dict[Player, LExpr]) -> Leaf:
    return Leaf(utilities)

class Condition(Tree):
    def __init__(self, conditions: Dict[Constraint, Tree]):
        self.conditions = conditions

    def json(self):
        return {
            'condition': [
                {'constraint': constraint.json(), 'child': child}
                for constraint, child in self.conditions.items()
            ]
        }

    def graphviz(self):
        print(f'\tn{id(self)} [label="Condition"];')
        for constraint, child in self.conditions.items():
            child.graphviz()
            print(f'\tn{id(self)} -> n{id(child)} [label="{constraint}"];')

def condition(conditions: Dict[Constraint, Tree]) -> Condition:
    return Condition(conditions)

class Branch(Tree):
    def __init__(self, player: Player, actions: Dict[Action, Tree], condition: Constraint=Truth()):
        self.player = player
        self.actions = actions

    def json(self):
        return {
            'player': self.player,
            'children': [
                {'action': action, 'child': child}
                for action, child in self.actions.items()
            ]
        }

    def graphviz(self):
        print(f'\tn{id(self)} [label="{self.player}"];')
        for (action, child) in self.actions.items():
            child.graphviz()
            print(f'\tn{id(self)} -> n{id(child)} [label="{action}"];')


def branch(player: Player, actions: Dict[Action, Tree]) -> Branch:
    return Branch(player, actions)


def players(*players: str) -> List[Player]:
    return [Player(player) for player in players]


def actions(*actions: str) -> List[Action]:
    return [Action(action) for action in actions]


def infinitesimals(*infs: str) -> List[Expr]:
    return [NameExpr(inf) for inf in infs]


def constants(*constants: str) -> List[Expr]:
    return [NameExpr(constant) for constant in constants]





def finish(
        players: List[Player],
        actions: List[Action],
        infinitesimals: List[Expr],
        constants: List[Expr],
        initial_constraints: List[Constraint],
        weak_immunity_constraints: List[Constraint],
        weaker_immunity_constraints: List[Constraint],
        collusion_resilience_constraints: List[Constraint],
        practicality_constraints: List[Constraint],
        honest_histories: List[HistoryTree],
        honest_utilities: List[HonestUtility],
        tree: Tree,
        file = None
):
    import sys
    mode = sys.argv[1] if len(sys.argv) >= 2 else ''
    if mode == 'graphviz':
        print("digraph tree {")
        tree.graphviz()
        print("}")
    elif file is None:
        json.dump({
            'players': players,
            'actions': actions,
            'infinitesimals': infinitesimals,
            'constants': constants,
            'initial_constraints': initial_constraints,
            'property_constraints': {
                'weak_immunity': weak_immunity_constraints,
                'weaker_immunity': weaker_immunity_constraints,
                'collusion_resilience': collusion_resilience_constraints,
                'practicality': practicality_constraints
            },
            'honest_histories': honest_histories,
            'honest_utilities': honest_utilities,
            'tree': tree
        }, default=lambda x: x.json(), fp=sys.stdout, indent=2)
        sys.exit(0)
    else:
        json.dump({
            'players': players,
            'actions': actions,
            'infinitesimals': infinitesimals,
            'constants': constants,
            'initial_constraints': initial_constraints,
            'property_constraints': {
                'weak_immunity': weak_immunity_constraints,
                'weaker_immunity': weaker_immunity_constraints,
                'collusion_resilience': collusion_resilience_constraints,
                'practicality': practicality_constraints
            },
            'honest_histories': honest_histories,
            'honest_utilities': honest_utilities,
            'tree': tree
        }, default=lambda x: x.json(), fp=file, indent=2)