# CheckMate

CheckMate automatically checks security properties of games.
It can analyze the following properties:

* weak immunity
* weaker immunity
* collusion resilience
* practicality

The modeling of protocols as games and manual analysis of security properties can be found in [1].
This and other related materials are listed below.

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
8. `honest_utilities`: in a subtree *off* the honest history, then we may need to know the honest utility from the parent tree
9. `tree`:  The tree defines the structure of the game. Each node in the game tree is either an internal node, a leaf, or a subtree. Each **internal node** is represented by a dictionary containing the keys
    * `player`: the name of the player whose turn it is, and
    * `children`: the list of branches the player can choose from. Each branch is encoded as yet another dictionary with the two keys `action` and `child`. The `action` key provides the action that the player has to take to reach the chosen branch of the tree. The other key `child` finally contains another tree node.
Each **leaf node** is encoded as a dictionary with the only key `utility`. As a leaf node represents one way of terminating the game, it contains the pay-off information for each player in this scenario. Hence, `utility` is a list containing the players' utilities. Therefore, each element is a dictionary with the two following keys:
    * `player`: the name of the player whose utility it specified, and
    * `value`: the utility for the player. This can be any term over an infinitesimal occurring in `infinitesimals`, a constant contained in `constants`, and reals.
Each **subtree** is a dictionary with exactly one key `subtree`. A subtree represents the *result* of analysing a subtree in the game, and is thus usually generated automatically. The value is another dictionary with values `honest_utilities` (the honest utilities, only relevant for the honest subtree), and property results `weak_immunity`, `weaker_immunity`, `collusion_resilience` and `practicality`. Practicality results are a list of cases and utilities for each case. Other security properties are a list of player groups together with utility requirements for that player group to conform with the property.

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

## Run

To run the security analysis, execute the following command from the `build` folder (where `GAME` is the path to the input file - for example, `examples/key_examples/closing_game.json`):

```shell
./checkmate GAME
```

There are several options:
* `--preconditions`: If a property is not satisfied, try to compute preconditions under which the property holds.
* `--counterexamples`: If a property is not fulfilled, provide a counterexample, i.e. "justifications" why the property does not hold, per analyzed property.
* `--all_counterexamples`: If a property is not fulfilled, provide **all** counterexamples for the considered problematic case(s). The number of considered problematic cases depends on whether the `all_cases` flag was set.
* `--all_cases`: If a property is not fulfilled, keep looking for all problematic cases.
* `--strategies`: If a property is satisfied, provide a witness strategy.
* If not all security properties should be analyzed, users can specify properties individually with some combination of `--weak_immunity`, `--weaker_immunity`, `--collusion_resilience`, and `--practicality`.
* `--subtree` should be used if the input is intended as part of a larger tree.

For instance, to run a security analysis on the Closing Game [1] with counterexample generation, but only considering weak immunity and collusion resilience, execute the following:

```shell
checkmate examples/key_examples/closing_game.json --counterexamples --weak_immunity --collusion_resilience
```

## Examples

Smaller examples are provided directly as JSON files, such as `market_entry_game.json`.
Others, such as the auction benchmark, are provided in forms of scripts that generate the benchmark - this may be more involved for extremely large games that generate temporary subtrees for analysis.

Important benchmarks include `closing_game.py` that models the Closing Game proposed in [1] for the closing phase of the [Bitcoin Lightning protocol](https://lightning.network/lightning-network-paper.pdf) as well as `routing_three.py`, which models the routing module of the Lightning protocol [1] for three users.
`routing_game-subtree-supertree.py` generates (compositionally, over several hours and with intermediate files) a supertree for four users, included for reference as `routing_game-four-supertree.json`.

## Relevant Publications

[[1]](https://doi.org/10.48550/arXiv.2109.07429) Sophie Rain, Georgia Avarikioti, Laura Kovács, Matteo Maffei.
Towards a Game-Theoretic Security Analysis of Off-Chain Protocols (CSF 2022).

[[2]](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
Automating Security Analysis of Off-Chain Protocols (Talk at [FMBC 2022](https://fmbc.gitlab.io/2022/)).

[[3]](https://doi.org/10.34726/hss.2022.104340) Lea Salome Brugger.
Automating Proofs of Game-Theoretic Security Properties of Off-Chain Protocols (Diploma Thesis, 2022).

[[4]](https://dl.acm.org/doi/10.1145/3576915.3623183) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
CheckMate: Automated Game-Theoretic Security Reasoning (CCS 2023).
