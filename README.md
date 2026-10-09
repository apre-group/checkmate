# CheckMate

CheckMate automatically checks security properties of games.
It can analyze the following properties:

* weak immunity
* weaker immunity
* collusion resilience
* practicality

The modeling of protocols as games is discussed in [1] and [4], and the manual analysis of security properties in [4].
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
Each **subtree** is a dictionary with exactly one key `subtree`. A subtree represents the *result* of analysing a subtree in the game, and is thus usually generated automatically (see [Compositional analysis](#compositional-analysis)). The value is another dictionary with values `honest_utility` (the utility at the end of the honest history inside the subtree, which the supertree needs; only relevant for the honest subtree, and not to be confused with the input key `honest_utilities`), and property results `weak_immunity`, `weaker_immunity`, `collusion_resilience` and `practicality`. Practicality results are a list of cases and utilities for each case. Other security properties are a list of player groups together with the cases in which the property holds for that player group. For collusion resilience, the list contains every group except the group of all players; if the subtree lies along the honest history, it also contains the empty group `[]`, which the supertree looks up when no player has deviated before reaching the subtree.

All **expressions** throughout the input support the following symbols in infix notation: `+`, `-`, `*`
(only if not both multiplicators are infinitesimal), `=`, `!=` (inequality), `<`, `>`, `<=` , `>=`, `|` (or).
To express the conjunction of two expressions, list both.
Additionally, all (real) numbers and all constants and infinitesimals declared in the dictionary are supported.

## Build

CheckMate is written in C++11. It requires:

* [CMake](https://cmake.org/) as a build system, although you could do without this in a pinch.
* The [Z3](https://github.com/Z3Prover/z3) SMT solver, via its API. To obtain the Z3 API, follow the directions in Z3's README or use a recent prebuilt package - Debian has `libz3-dev`, Red Hat has `z3-devel`.
* To generate some of the examples, [Python 3](https://www.python.org/downloads/) has to be installed as well.

We also use [JSON for modern C++](https://json.nlohmann.me/), but this is already vendored in the source tree as `src/json.hpp`.

Assuming that you have a working compiler, CMake, and both Z3 headers and libraries, you can follow a standard CMake build. On a UNIX-like operating system:

```shell
mkdir build # build CheckMate into this directory
cmake -B build -DCMAKE_BUILD_TYPE=Release # configure CheckMate: you likely want a release build
make -C build # actually compile CheckMate with make(1)
```

You will then have a CheckMate binary in the `build` folder.

Troubleshooting:
* CMake 4 refuses to configure projects that declare compatibility with CMake versions older than 3.5. Add `-DCMAKE_POLICY_VERSION_MINIMUM=3.5` to the `cmake` call.
* On macOS, linking can fail with `unknown architecture` errors in `.tbd` files if the Command Line Tools ship an SDK newer than their linker. Update the Command Line Tools, or point CMake to an older SDK, e.g. `-DCMAKE_OSX_SYSROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX26.sdk`.
* If Z3 is installed in a non-standard location (e.g. Homebrew on Apple Silicon), pass its paths: `-DCMAKE_CXX_FLAGS=-I/opt/homebrew/include -DCMAKE_EXE_LINKER_FLAGS=-L/opt/homebrew/lib`.

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
* If not all security properties should be analyzed, users can specify properties individually with some combination of `--weak_immunity`, `--weaker_immunity`, `--collusion_resilience`, and `--practicality`.
* `--subtree` is used for [compositional analysis](#compositional-analysis). It cannot be combined with `--counterexamples`, `--all_counterexamples`, `--strategies` or `--preconditions`.
* `--count_nodes` and `--count_calls`: For experiments, report the number of checked tree nodes and of SMT solver calls per analyzed property.

For instance, to run a security analysis on the Closing Game [4] with counterexample generation, but only considering weak immunity and collusion resilience, execute the following from the repository root:

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

1. Write the subtree as an input file of its own. If it lies along the honest history, give the rest of the honest history in `honest_histories`; otherwise give the honest utility of the whole game in `honest_utilities`.
2. Run `./checkmate SUBTREE --subtree`. The results are written to `SUBTREE.out`.
3. In the supertree, replace the subtree by a node `{"subtree": ...}` containing the `subtree` dictionary from `SUBTREE.out`, and run `./checkmate SUPERTREE` as usual. Whenever the tree contains subtree results, counterexamples and strategies end at the subtrees, with a hint to run the subtree on its own.

Subtrees may again contain subtrees, so results can be nested.
Collusion resilience results of subtrees must have been computed with the current version of CheckMate: results from older versions do not contain the empty group, and need not be consistent with the current way groups are checked.

## Examples

Smaller examples are provided directly as JSON files, such as `market_entry_game.json`.
Others, such as the auction benchmark, are provided in forms of scripts that generate the benchmark - this may be more involved for extremely large games that generate temporary subtrees for analysis.

Important benchmarks include `closing_game.py` that models the Closing Game proposed in [4] for the closing phase of the [Bitcoin Lightning protocol](https://lightning.network/lightning-network-paper.pdf) as well as `routing_game-three.py`, which models the routing module of the Lightning protocol [4] for three users.
`routing_game-subtree-supertree.py` generates (compositionally, over several hours and with intermediate files) a supertree for four users, included for reference as `routing_game-four-supertree.json`.
Its collusion resilience subtree results were computed with an older version of CheckMate; regenerate it with the script before analyzing it.

Examples for compositional analysis are the `*-subtree*.json` files together with the corresponding `*-supertree.json` files, e.g. `closing_game-subtree1.json` to `closing_game-subtree8.json` with `closing_game-supertree.json`, or `pirate_game-subtree-Sc-not-honest.json`, whose results are nested in `pirate_game-subtree-Sb-honest.json` and `pirate_game-subtree-Sb-not-honest.json`, which in turn are part of `pirate_game-supertree.json`.

## Relevant Publications

[[1]](https://doi.org/10.1007/978-3-032-10794-7_18) Sophie Rain, Anja Petković Komel, Michael Rawson, Laura Kovács.
Game Modeling of Blockchain Protocols (iFM 2025).

[[2]](https://doi.org/10.1145/3763120) Ivana Bocevska, Anja Petković Komel, Laura Kovács, Sophie Rain, Michael Rawson.
Divide and Conquer: A Compositional Approach to Game-Theoretic Security (OOPSLA 2025).

[[3]](https://dl.acm.org/doi/10.1145/3576915.3623183) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
CheckMate: Automated Game-Theoretic Security Reasoning (CCS 2023).

[[4]](https://doi.org/10.48550/arXiv.2109.07429) Sophie Rain, Georgia Avarikioti, Laura Kovács, Matteo Maffei.
Towards a Game-Theoretic Security Analysis of Off-Chain Protocols (CSF 2023).

[[5]](https://doi.org/10.34726/hss.2022.104340) Lea Salome Brugger.
Automating Proofs of Game-Theoretic Security Properties of Off-Chain Protocols (Diploma Thesis, 2022).

[[6]](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
Automating Security Analysis of Off-Chain Protocols (Talk at [FMBC 2022](https://fmbc.gitlab.io/2022/)).
