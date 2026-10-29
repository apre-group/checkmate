# CheckMate

CheckMate automatically checks security properties of games.
It can analyze the following properties:

* weak immunity
* weaker immunity
* collusion resilience
* practicality

The modeling of protocols as games is discussed in [1] and [5], and the manual analysis of security properties in [5].
This and other related materials are listed below.

For **weak immunity**, CheckMate checks for every player whether there is a strategy along the honest history
that guarantees them a non-negative utility, no matter what the other players do.
Off the honest history, the strategy may choose any action that keeps the player's utility non-negative.
**Weaker immunity** is the same, except that infinitesimals are ignored: only the non-infinitesimal part of the utility has to be non-negative.

For **collusion resilience**, CheckMate checks whether there is a single strategy along the honest history
such that no group of players (except the group of all players) can deviate profitably,
i.e. obtain a higher joint utility than on the honest history.
Groups grow as players deviate: once a player deviates, every later check includes them,
and a leaf is compared to the honest utility for every group containing the players that deviated on the way there.

For **practicality**, CheckMate checks whether the honest history is a subgame perfect equilibrium:
working backwards from the leaves, in every subgame each player chooses an action maximizing their utility,
and along the honest history no player can obtain a higher utility by deviating from the honest action.

CheckMate also analyzes **conditional extensive form games (CEFGs)**: games in which some constants are unknown to the players
until a *condition node* reveals them, e.g. prices or exchange rates that change during the game (see [Conditional games](#conditional-games-cefgs)).
CheckMate decides from the input which kind of game it is given and analyzes it accordingly.

The input for CheckMate is a JSON file representing a game with its initial constraints.
The expected structure is explained in [the section below](#input).
Examples for such instances can be found in the `examples` folder, alongside scripts to generate some instances.

## Input

We support an extension of the original CheckMate input format, i.e. a dictionary with the following keys:
1. `players`: expects the list of all players in the game.
2. `actions`: expects the list of all possible actions throughout the game.
3. `infinitesimals`: lists all symbolic values occurring in the utilities that are supposed to be treated as inferior to the other symbolic values.
4. `constants`: lists all the regular symbolic values occurring in the utilities. Note that all symbolic values in the utilities have to be included either in the `infinitesimals` or the `constants` list.
5. `initial_constraints`: CheckMate allows users to specify initial constraints enforced on the otherwise unconstrained symbolic values in the utilities.
6. `property_constraints`: The user also has the opportunity to define further initial constraints, which will be only assumed for a specific security property, hence the name. This feature allows the user to specify the weakest possible assumptions for each property.
7. `honest_histories`: Users are required to provide at least one terminal history as the honest history, which is (one of) the desired course(s) of actions of the game. This is the behavior CheckMate (dis-)proves game-theoretic security for. If more than one honest history is listed, CheckMate analyzes one after the other.
8. `honest_utilities`: only for analysing a subtree *off* the honest history with `--subtree`: the honest utility of the whole game, which lies outside the subtree.
9. `tree`:  The tree defines the structure of the game. Each node in the game tree is either an internal node, a leaf, or a subtree. Each **internal node** is represented by a dictionary containing the keys
    * `player`: the name of the player whose turn it is, and
    * `children`: the list of branches the player can choose from. Each branch is encoded as yet another dictionary with the two keys `action` and `child`. The `action` key provides the action that the player has to take to reach the chosen branch of the tree. The other key `child` finally contains another tree node.
Each **leaf node** is encoded as a dictionary with the only key `utility`. As a leaf node represents one way of terminating the game, it contains the pay-off information for each player in this scenario. Hence, `utility` is a list containing the players' utilities. Therefore, each element is a dictionary with the two following keys:
    * `player`: the name of the player whose utility it specified, and
    * `value`: the utility for the player. This can be any term over an infinitesimal occurring in `infinitesimals`, a constant contained in `constants`, and reals.
Each **subtree** is a dictionary with exactly one key `subtree`. A subtree represents the *result* of analysing a subtree in the game, and is thus usually generated automatically (see [Compositional analysis](#compositional-analysis)). The value is another dictionary with values `honest_utility` (the utility at the end of the honest history inside the subtree, which the supertree needs; only relevant for the honest subtree, and not to be confused with the input key `honest_utilities`), and property results `weak_immunity`, `weaker_immunity`, `collusion_resilience` and `practicality`. Practicality results are a list of cases and utilities for each case. Other security properties are a list of player groups together with the cases in which the property holds for that player group. For collusion resilience, the list contains every group except the group of all players, including the empty group `[]`, which the supertree looks up when no player has deviated before reaching the subtree.

Games with condition nodes are described in [Conditional games](#conditional-games-cefgs).

All **expressions** throughout the input support the following symbols in infix notation: `+`, `-`, `*`
(only if not both multiplicators are infinitesimal), `=`, `!=` (inequality), `<`, `>`, `<=` , `>=`, `|` (or).
To express the conjunction of two expressions, list both.
Additionally, all (real) numbers and all constants and infinitesimals declared in the dictionary are supported.

### Compact format

CheckMate also reads a compact, line-based format, which is easier to write and read than JSON.
Here is the game of `examples/key_examples/splits_wi.json`:

```
players: D, G
constants: a, b
initial: a > 0
honest: q
honest: l r
honest: l y

D
  q -> D: a, G: a
  l -> G
    r -> D: a, G: b
    y -> D: a, G: -b
```

The header lines are `players:`, `constants:` and `infinitesimals:` (comma-separated names), and then one line per constraint or history:
`initial:` for an initial constraint, `weak_immunity:`, `weaker_immunity:`, `collusion_resilience:` or `practicality:` for a property constraint, `honest:` for an honest history (actions separated by spaces), and `honest_utility:` for an honest utility (`PLAYER: utility, ...`).
The tree starts at the first line that is not a header: the player at the root, and then one line per branch, indented below its node: `action -> PLAYER` for an internal node (whose branches follow, indented further), `action -> PLAYER: utility, ...` for a leaf, or `action -> subtree {...}` for a subtree result in JSON.
The `actions` list is not needed; it is derived from the tree. `#` starts a comment.

[Conditional games](#conditional-games-cefgs) have a compact form as well:

```
players: A, B
unknown_constants: y
initial: y = 0 | y = 1
honest: dev risk {if y = 0 -> l; if y = 1}

A
  hon -> A: 2, B: 0
  dev -> A
    safe -> A: 1, B: 0
    risk -> ? reveals y
      if low: y = 0 -> B
        l -> A: 1, B: 1
        r -> A: 0, B: 2
      if y = 1 -> A: 3, B: 0
```

Unknown constants and infinitesimals are declared with `unknown_constants:` and `unknown_infinitesimals:`.
A condition node is `?` (`action -> ?`, or `?` at the root), or `? reveals CONSTANT, ...` to reveal further unknowns, and its conditions follow, indented below it: `if CONDITION -> ...`, or `if NAME: CONDITION -> ...` for a named condition, followed by a node as after `action ->`.
At a condition node, an honest history continues in every condition, in braces at its end: `{if CONDITION -> history; ...}`, where `if CONDITION` alone is a condition after which the history ends.
An honest utility that depends on conditions is written in the same way: `honest_utility: {if CONDITION -> PLAYER: utility, ...; ...}`.

CheckMate treats a file as JSON if it starts with `{`, and as the compact format otherwise.
`build/checkmate-convert GAME [OUTPUT]` converts a game from one format to the other.

### Validation

Before analyzing a game, CheckMate checks that it is well-formed, in either format: 
- every name is declared once (and not both as a constant and as an infinitesimal), 
- every internal node has children with distinct actions, 
- every leaf has exactly one utility per player, 
- all utilities and constraints parse,
- every honest history exists in the tree and ends at a leaf or a subtree.
A game with honest utilities instead of honest histories (a subtree off the honest history) is accepted as well.
For conditional games, CheckMate also checks that:
- constants and infinitesimals are a list or `{"known": [...], "unknown": [...]}`,
- every condition node has at least one condition, each with a constraint and a child, and no condition twice,
- `reveals` names only constants declared unknown,
- the utilities at a leaf use only known constants and the unknowns revealed on the way to it,
- an honest history gives, at a condition node, a path for each of its conditions, as its last element.

Conditions in an honest history are matched to those of the condition node by CheckMate itself, which reports conditions that are not in the node.

For conditional games, CheckMate then checks the conditions of every condition node with Z3. The checks use the initial constraints, the constraints of each analyzed property, and the conditions on the way to the node:
- the conditions are mutually exclusive: no two of them hold for the same values,
- the conditions leave no gap: for all values, one of them holds,
- at least one of the conditions can hold.

The constraints may rule out some of the conditions of a node, e.g. to try out what happens for a narrower range of values, but not all of them; CheckMate prints a note for every condition that can never hold and does not check the nodes below it:

```
checkmate: note: condition 2 (x < 0.0) of the condition node after hon can never hold (given the initial constraints and the conditions on the way)
checkmate: game.json: condition 1 (x >= 0.0) and condition 2 (x <= 0.0) of the condition node after hon overlap: both hold for some values (given the initial constraints and the conditions on the way) (turn this check off with --no_validate_conditions)
```

`--no_validate_conditions` turns these checks off and keeps only the checks of the input format above. If Z3 cannot decide a check within 10 seconds, CheckMate warns and goes on.

If a check fails, CheckMate stops with an error naming the line in the compact format, or the node in JSON:

```
checkmate: game.txt: line 2: q already ends at a leaf, but the honest history continues with x
checkmate: game.json: node at b: action c appears twice
```

CheckMate also stops with an error if the initial constraints together with the constraints of a property are unsatisfiable, since every property would then hold vacuously.

## Build

CheckMate is written in C++17. It requires:

* [CMake](https://cmake.org/) 3.25 or newer as a build system, although you could do without this in a pinch.
* The [Z3](https://github.com/Z3Prover/z3) SMT solver, via its API. To obtain the Z3 API, follow the directions in Z3's README or use a recent prebuilt package - Debian has `libz3-dev`, Red Hat has `z3-devel`.
* To generate some of the examples, [Python 3](https://www.python.org/downloads/) has to be installed as well.
* Optionally, [cvc5](https://cvc5.github.io/) for practicality of some conditional games (see [Conditional games](#conditional-games-cefgs)).

We also use [JSON for modern C++](https://json.nlohmann.me/), but this is already vendored in the source tree as `src/json.hpp`.

Assuming that you have a working compiler, CMake, and both Z3 headers and libraries, you can follow a standard CMake build. On a UNIX-like operating system:

```shell
mkdir build # build CheckMate into this directory
cmake -B build -DCMAKE_BUILD_TYPE=Release # configure CheckMate: you likely want a release build
make -C build # actually compile CheckMate with make(1)
```

You will then have a CheckMate binary in the `build` folder.

Troubleshooting:
* On macOS, linking can fail with `unknown architecture` errors in `.tbd` files if the Command Line Tools ship an SDK newer than their linker. Update the Command Line Tools, or point CMake to an older SDK, e.g. `-DCMAKE_OSX_SYSROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX26.sdk`.
* If Z3 is installed in a non-standard location (e.g. Homebrew on Apple Silicon), pass its paths: `-DCMAKE_CXX_FLAGS=-I/opt/homebrew/include -DCMAKE_EXE_LINKER_FLAGS=-L/opt/homebrew/lib`.

### In the browser

`html/` contains a page that runs CheckMate in the browser, compiled to WebAssembly: pick an example or paste a game, run it, and see the verdicts, cases, strategies and counterexamples drawn on the game tree.
To build it, install [Emscripten](https://emscripten.org/), get the [Z3](https://github.com/Z3Prover/z3) sources, and run, from the repository root:

```shell
source /path/to/emsdk/emsdk_env.sh
scripts/build_emscripten.sh /path/to/z3 [/path/to/cvc5]   # builds Z3 (and cvc5) for WebAssembly once, then CheckMate
cd html && python3 -m http.server                         # then open http://localhost:8000
```

With the [cvc5](https://github.com/cvc5/cvc5) sources (which need Emscripten 6.0.8 or later), the page also uses cvc5 for the practicality of conditional games, as CheckMate does (see [Conditional games](#conditional-games-cefgs)); it loads cvc5 only for runs of conditional games that check practicality.
The page must be served over HTTP (not opened as a file), but needs no special server headers.

## Run

To run the security analysis, execute the following command from the `build` folder (where `GAME` is the path to the input file - for example, `../examples/key_examples/market_entry_game.json`):

```shell
./checkmate GAME
```

There are several options:
* `--preconditions`: If a property is not satisfied, try to compute preconditions under which the property holds.
* `--counterexamples`: If a property is not fulfilled, provide a counterexample, i.e. "justifications" why the property does not hold, per analyzed property.
* `--all_counterexamples`: If a property is not fulfilled, provide **all** counterexamples for the considered problematic case(s). The number of considered problematic cases depends on whether the `all_cases` flag was set. For collusion resilience, identical counterexamples are shown only once, and at most 100 counterexamples are shown per case.
* `--all_cases`: If a property is not fulfilled, keep looking for all problematic cases.
* `--strategies`: If a property is satisfied, provide a witness strategy.
* `--json-out FILE`: Also write the results as JSON to `FILE`: for each honest history and property, the verdict, every case checked (as a list of SMT-LIB 2 conditions) with whether the property holds in it, the strategies and counterexamples, exactly when the text output shows them, and the weakest precondition with `--preconditions`. With `--subtree`, `FILE` gets the subtree result instead: the same as `SUBTREE.out`, but with cases as SMT-LIB 2 conditions and utilities as SMT-LIB 2 real and infinitesimal parts.
* If not all security properties should be analyzed, users can specify properties individually with some combination of `--weak_immunity`, `--weaker_immunity`, `--collusion_resilience`, and `--practicality`.
* `--subtree` is used for [compositional analysis](#compositional-analysis). For games without condition nodes, it cannot be combined with `--counterexamples`, `--all_counterexamples`, `--strategies` or `--preconditions`.
* `--no_validate_conditions`: Only for conditional games: do not check that the conditions of every condition node are mutually exclusive, leave no gap, and can hold (see [Validation](#validation)). For games without condition nodes, CheckMate warns and ignores it.
* `--count_nodes` and `--count_calls`: For experiments, report the number of checked tree nodes and of SMT solver calls per analyzed property.
* `--no-cr-node-cache`, `--no-cr-leaf-cache`, `--no-cr-implied-groups`, `--no-cr-violated-lookup`, `--no-problematic-groups`, `--exact-splits`, `--reset-from-root`: For testing only, disable an optimization or heuristic. Results must not change; the fuzzer (`scripts/fuzz.py`, see [FUZZING.md](FUZZING.md)) checks this.

For conditional games, only the properties, `--subtree`, `--json-out` and `--no_validate_conditions` are available so far: `--counterexamples`, `--all_counterexamples`, `--strategies` and `--preconditions` are not yet implemented for them, and `--all_cases`, `--count_nodes`, `--count_calls` and the testing options only apply to games without condition nodes.
With `--json-out`, the JSON result of a conditional game has one entry per run and property, as for other games but without cases: `history` is the honest history analysed (in the input format, with conditions in CheckMate's syntax, and continued into subtree nodes), with the index of the honest history in `honest_histories` under `honest_history` (several runs share an index if the history ends in a subtree node with several honest histories inside), or `null` for the runs without honest history, which have the index of the honest utility under `honest_utility` for collusion resilience, and `holds` is `true`, `false`, or `null` if practicality could not be decided, with the reason under `undecided`. With `--subtree`, `FILE` gets `{"version": 1, "subtree": ...}` with the same list as `SUBTREE.out`.
CheckMate prints a warning for each such option and ignores it, e.g. `checkmate: --counterexamples is not yet implemented for CEFGs and is ignored`.

For instance, to run a security analysis on the Closing Game [5] with counterexample generation, but only considering weak immunity and collusion resilience, execute the following from the repository root:

```shell
python3 examples/key_examples/closing_game.py > closing_game.json
build/checkmate closing_game.json --counterexamples --weak_immunity --collusion_resilience
```

## Counterexamples

### Weak immunity counterexamples

A counterexample for weak (or weaker) immunity describes how the other players can harm one player, i.e. force a negative utility on them, whatever that player does.
For example, for history `[r_A, l_B]` of `running_example.json`:

```
Counterexample for case: [((a - 2.0) >= 0.0), (b < 0.0)]
Player A can be harmed, if
	Player B takes one of the actions [r_B] after history [r_A]
```

Each line lists the actions of another player that lead to harm after the given history.
The harmed player follows the honest history; after leaving it, all of their choices are covered, and each one leads to harm.
With `--all_counterexamples`, a line can list several actions, each of which leads to harm.
If the honest history itself yields a negative utility, the counterexample reads `Player P is harmed, if they follow the honest history`.

### Collusion resilience counterexamples

A counterexample for collusion resilience describes how a group of players can deviate profitably in a case where the property is violated.
For example, for history `[e, s]` of `market_entry_game.json`:

```
Counterexample for case: []
	Player E deviates to [i] after history [e]
	After history [e, i]: group [E] gains more than on the honest history
```

The first line is the deviation from the honest history.
Further lines of the form `Player P chooses [a] after history h` are choices the deviating players make afterwards (no action is prescribed there anymore).
Players that act after the deviation without being listed stay honest: the counterexample covers all of their choices, and they are never part of a group.
Finally, the counterexample lists every leaf reached, together with all groups that obtain a higher joint utility there than on the honest history.
If the game contains subtree results, a counterexample can end in a subtree; run that subtree on its own with `--counterexamples` to see the rest.

### Practicality counterexamples

A counterexample for practicality shows a player who is better off deviating from the honest history.
For example, for history `[o]` of `market_entry_game.json`:

```
Counterexample for case: []
For player N all practical histories after [e] yield a better utility than the honest one.
Practical histories:
[e, i]
```

Here, player N deviates from the honest history by choosing `e` at the root.
Afterwards, all players continue practically, i.e. in a subgame perfect way, which leads to the listed practical histories.
Each of them gives N a higher utility than the honest history.
If the game contains subtree results, the counterexample can instead say that a subtree is not practical; run that subtree on its own with `--counterexamples` to see the rest.

### Compositional analysis

Large games can be analyzed in parts [2]: subtrees are analyzed on their own, and their results replace them in a smaller supertree.

1. Write the subtree as an input file of its own. If it lies along the honest history, give the rest of the honest history in `honest_histories`; otherwise give the honest utility of the whole game in `honest_utilities`. Its initial constraints are those of the supertree, together with all conditions of condition nodes on the way to the subtree in the supertree; its property constraints are those of the supertree. A subtree below a condition that the constraints of the supertree rule out is never reached and need not be analyzed.
2. Run `./checkmate SUBTREE --subtree`. The results are written to `SUBTREE.out`.
3. In the supertree, replace the subtree by a node `{"subtree": ...}` containing the `subtree` dictionary from `SUBTREE.out`, and run `./checkmate SUPERTREE` as usual. Whenever the tree contains subtree results, counterexamples and strategies end at the subtrees, with a hint to run the subtree on its own.

Subtrees may again contain subtrees, so results can be nested.
A subtree without condition nodes may be part of a conditional supertree: its results (a dictionary, see [Input](#input)) are read by the analysis of conditional games as well.
The constants in them have to be known at the subtree in the supertree; a subtree in which some constants are still unknown, or whose honest utility in `honest_utilities` depends on conditions of the supertree (see below), has to be analyzed as a conditional game.
The results of a conditional subtree are a list instead (see [Conditional games](#conditional-games-cefgs)), so a supertree containing them is analyzed as a conditional game.
Collusion resilience results of subtrees must have been computed with the current version of CheckMate: results from older versions may lack the empty group (CheckMate then stops with an error asking to recompute the subtree), and need not be consistent with the current way groups are checked.

## Conditional games (CEFGs)

A conditional game extends the input as follows.
- `constants` (and `infinitesimals`) can be a dictionary `{"known": [...], "unknown": [...]}`: unknown constants are not known to the players until they are revealed.
- A **condition node** is a dictionary with the key `condition`: a list of dictionaries with the keys `constraint` (an expression over the constants), `child` (the tree node after it) and optionally `name`. The constraints have to be mutually exclusive and cover all values allowed by the initial constraints and the conditions on the way to the node; the constraints may rule out some of them, but not all (CheckMate checks this, see [Validation](#validation)). The unknown constants occurring in the constraints are revealed at the node, as are those listed in the optional key `reveals`. Utilities may only use constants that are known at their leaf.
- An honest history continues in every condition of a condition node: at a condition node, it contains a list of dictionaries `{"condition": ..., "path": [...]}`, one per condition, with the rest of the honest history after it.
- An honest utility in `honest_utilities` can likewise depend on conditions: its `utility` is then a list of dictionaries `{"condition": ..., "utility": [...]}`.

CheckMate treats a game as conditional if it has a condition node, declares unknown constants, contains results of a conditional subtree, or has an honest utility that depends on conditions; it then prints e.g. `Game type: CEFG (condition nodes)`. Conditional games can be written in the [compact format](#compact-format) as well.

Practicality of a conditional game may depend on how players break ties for different revealed values. If Z3 cannot decide this within 10 seconds, CheckMate asks [cvc5](https://cvc5.github.io/) to synthesize the tie-breaking (as `cvc5` on the `PATH`, or the program in the environment variable `CHECKMATE_CVC5`), for at most 20 minutes; in the browser, if the page was built with cvc5, it runs cvc5 compiled to WebAssembly instead (where its time limit is checked only between its steps, so it may take longer to stop). If neither decides it, the answer is `UNKNOWN` with the reason.

With `--subtree`, the results of a conditional game are written to `GAME.out` as a list of entries, one for every honest history (`honest_history`) and honest utility (`honest_utility`) analyzed, and one without honest history (`no_honest_history`), each with the results in `subtree`. The whole list is the value of the subtree node in the supertree.

The examples are in `examples/conditional_actions`, generated by Python scripts. `scripts/run_cefg_regressions.sh` runs them and compares the results with `tests/cefg_regressions/expected.txt`, as `scripts/run_regressions.sh` does for the other games.

## Examples

Smaller examples are provided directly as JSON files, such as `market_entry_game.json`.
Others, such as the auction benchmark, are provided in forms of scripts that generate the benchmark - this may be more involved for extremely large games that generate temporary subtrees for analysis.

Important benchmarks include `closing_game.py` that models the Closing Game proposed in [5] for the closing phase of the [Bitcoin Lightning protocol](https://lightning.network/lightning-network-paper.pdf) as well as `routing_game-three.py`, which models the routing module of the Lightning protocol [5] for three users.
`routing_game-subtree-supertree.py` generates (compositionally, over several hours and with intermediate files) a supertree for four users, included for reference as `routing_game-four-supertree.json`.
CheckMate currently rejects that file, since many of its nodes have two children with the same action (see [Validation](#validation)).
Run the script from the `build` folder: it analyzes each of its 1440 subtrees with `./checkmate --subtree` and writes the supertree to `routing_game-supertree.json` there.
Its intermediate files are temporary files that are not deleted afterwards; set `TMPDIR` to a folder of your choice to remove them easily (they take up about 150 GB).

Examples for compositional analysis are the `*-subtree*.json` files together with the corresponding `*-supertree.json` files, e.g. `closing_game-subtree1.json` to `closing_game-subtree8.json` with `closing_game-supertree.json`, or `pirate_game-subtree-Sc-not-honest.json`, whose results are nested in `pirate_game-subtree-Sb-honest.json` and `pirate_game-subtree-Sb-not-honest.json`, which in turn are part of `pirate_game-supertree.json`.

## Relevant Publications

[[1]](https://doi.org/10.1007/978-3-032-10794-7_18) Sophie Rain, Anja Petković Komel, Michael Rawson, Laura Kovács.
Game Modeling of Blockchain Protocols (iFM 2025).

[[2]](https://doi.org/10.1145/3763120) Ivana Bocevska, Anja Petković Komel, Laura Kovács, Sophie Rain, Michael Rawson.
Divide and Conquer: A Compositional Approach to Game-Theoretic Security (OOPSLA 2025).

[[3]](https://easychair.org/publications/paper/6ZDH) Sophie Rain, Lea Salome Brugger, Anja Petković Komel, Laura Kovács, Michael Rawson.
Scaling CheckMate for Game-Theoretic Security (LPAR 2024).

[[4]](https://dl.acm.org/doi/10.1145/3576915.3623183) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
CheckMate: Automated Game-Theoretic Security Reasoning (CCS 2023).

[[5]](https://doi.org/10.48550/arXiv.2109.07429) Sophie Rain, Georgia Avarikioti, Laura Kovács, Matteo Maffei.
Towards a Game-Theoretic Security Analysis of Off-Chain Protocols (CSF 2023).

[[6]](https://doi.org/10.34726/hss.2022.104340) Lea Salome Brugger.
Automating Proofs of Game-Theoretic Security Properties of Off-Chain Protocols (Diploma Thesis, 2022).

[[7]](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
Automating Security Analysis of Off-Chain Protocols (Talk at [FMBC 2022](https://fmbc.gitlab.io/2022/)).
