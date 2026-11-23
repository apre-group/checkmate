// The JSON game format (see README.md), as far as the page uses it.

export interface Utility {
    player: string;
    value: string | number;
}

// a condition of a condition node (CEFGs), or a branch of a player's node
export interface Condition {
    constraint: string;
    name?: string;
    description?: string;
    child: TreeNode;
}
export interface Branch {
    action: string;
    description?: string;
    child: TreeNode;
}

// a step below a node in a history: an action, or {c: index} for a condition, so it cannot be taken for an action
export type Step = string | { c: number };

export interface TreeNode {
    player?: string;
    children?: Branch[];
    // condition nodes; older versions of examples/dsl.py write "condition": "True" on every node
    condition?: Condition[] | string;
    reveals?: string[];
    utility?: Utility[];
    subtree?: unknown;
    // set by the page while drawing
    _leaves?: number;
    _hist?: Step[];
    _text?: string[];
    _depth?: number;
    _folded?: boolean;
    _revealed?: string[];
    _x?: number;
    _desc?: string;
}

export type Declarations = string[] | { known?: string[]; unknown?: string[] };

// an element of an honest history: an action, or at a condition node of a CEFG, the history under each condition
export type HistoryElement = string | { condition: string; path: HistoryElement[] }[];

export interface Game {
    players: string[];
    actions?: string[];
    constants?: Declarations;
    infinitesimals?: Declarations;
    initial_constraints?: string[];
    property_constraints?: Record<string, string[]>;
    honest_histories?: HistoryElement[][];
    honest_utilities?: { utility: (Utility | { condition: string })[] }[];
    descriptions?: Record<string, string>;
    tree: TreeNode;
}

// --json-out results, one per property and honest history
export interface Choice {
    player: string;
    history: string[];
    actions: string[];
}
export interface Counterexample {
    case: string[];
    choices: Choice[];
    cr_leaves?: { groups: string[][]; history: string[]; subtree: boolean }[];
    cr_more_omitted?: boolean;
    player_group: string[];
}
export interface Strategy {
    case: string[];
    strategy: { player: string; history: string[]; action: string }[];
}
export interface Result {
    property: string;
    history?: HistoryElement[];
    honest_utility?: number;
    // null if practicality of a CEFG could not be decided
    holds: boolean | null;
    undecided?: string;
    cases?: { case: string[]; holds: boolean }[];
    strategies?: Strategy[];
    counterexamples?: Counterexample[];
    precondition?: string;
}
