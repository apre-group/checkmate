# CheckMate

CheckMate is a framework designed to automatically check security properties of games modeling off-chain (blockchain) protocols.
The framework analyzes the following properties:

* weak immunity
* weaker immunity
* collusion resilience
* practicality

The modeling of protocols as games and manual analysis of security properties can be found in [1].
This and other related materials are listed below.

The input for CheckMate is a CIF (=CheckMate Input Format) file representing a game. The CIF is explained in the Input section below.
Examples for such instances can be found in the `examples` folder.

## Input

The CheckMate Input Format CIF is a special instance of the JSON format. It is a dictionary with the following keys:

1. `players`: expects the list of all players in the game.
2. `actions`: expects the list of all possible actions throughout the game.
3. `infinitesimals`: lists all symbolic values occurring in the utilities that are supposed to be treated as inferior to the other symbolic values.
4. `constants`: lists all the regular symbolic values occurring in the utilities. Note that all symbolic values in the utilities have to be listed as either `infinitesimal` or `constant`.
5. `initial_constraints`: CheckMate allows users to specify initial constraints enforced on the otherwise unconstrained symbolic values in the utilities.
6. `property_constraints`: The user also has the opportunity to define further initial constraints, which will be only assumed for a specific security property, hence the name. This feature allows the user to specify the weakest possible assumptions for each property.
7. `honest_histories`: Users are required to provide at least one terminal history as the honest history, which is (one of) the desired course(s) of actions of the game. This is the behavior CheckMate (dis-)proves game-theoretic security for. If more than one honest history is listed, CheckMate analyzes one after the other.
8. `tree`:  The tree defines the structure of the game. Each node in the game tree is either an internal node or a leaf. Each **internal node** is represented by a dictionary containing the keys
    * `player`: the name of the player whose turn it is, and
    * `children`: the list of branches the player can choose from. Each branch is encoded as yet another dictionary with the two keys `action` and `child`. The `action` key provides the action that `player` has to take to reach the chosen branch of the tree. The other key `child` finally contains another tree node.
Each **leaf node** is encoded as a dictionary with the only key `utility`. As a leaf node represents one way of terminating the game, it contains the pay-off information for each player in this scenario. Hence, `utility` is a list containing the players' utilities. Therefore, each element is a dictionary with the two following keys:
    * `player`: the name of the player whose utility it specified, and
    * `value`: the utility of `player`. This can be any term over `infinitesimals`, `constants`, and reals.

All **arithmetic expressions** throughout the CIF support the following symbols in infix notation: +, -, * (only if not both multiplicators are infinitesimal), =, != (inequality), <, >, <= , >=, | (or). To express the conjunction of two expressions, just list both of them. Additionally, all (real) numbers and all constants and infinitesimals declared in the dictionary are supported.

## Prerequisites

 **************************@Michael: add the new stuff here (python 3 is still required to generate the bigger example games)******************* 
In order to run CheckMate, you need Python >= 3.8 with the [`z3-solver` package](https://pypi.org/project/z3-solver/) installed.
To acquire the required packages, run `pip install -r requirements.txt` in this directory.

### Run

To run the security analysis, execute the following command (where `GAME` is the path to the input file - for example, `../examples/key_examples/closing_game.cif`):

```
./checkmate GAME
```

There are several options, which can combined arbitrarily:

* `--preconditions`: If a property is not satisfied, try to compute preconditions under which the property holds. By default, this option is set to `false`.
* `--counterexamples`: If a property is not fulfilled, provide a counterexample, i.e. "justifications" why the property does not hold, per analyzed property.  By default, this option is set to `false`.
* `--all_counterexamples`: If a property is not fulfilled, provide **all** counterexamples for the considered problematic case(s). The number of considered problematic cases depends on whether the `all_cases` flag was set. By default, this option is set to `false`.
* `--all_cases`: If a property is not fulfilled, keep looking for all problematic cases. By default, this option is set to `false`.
* `--strategies`: If a property is satisfied, provide an evidence strategy that proves it.
* Additionally, if not all of the security properties (weak immunity, weaker immunity, collusion resilience, practicality) shall be analyzed, the user can specify the properties to be checked by setting the flag(s) `--weak_immunity`, `--weaker_immunity`, `--collusion_resilience`, respectively `--practicality`. Listing all 4 is equivalent to listing none since by default, all properties are analyzed.

For instance, to run a security analysis on the Closing Game [1] with counterexample generation, but only considering weak immunity and collusion resilience, execute the following command:

```
./checkmate ../examples/key_examples/closing_game.cif --counterexamples --weak_immunity --collusion_resilience
```

## Examples

All benchmarks can be found in the `examples` folder. The ones used for our LPAR2024 submission are in the `key_examples` folder.
The smaller ones are provided directly as CIF files, such as `market_entry_game.cif`. Others, such as the auction benchmark, are provided in forms of scripts that -- once executed -- generate the according CIF file. To generate the CIF document for a game `GAME.py` in the folder, run

```
python3 GAME.py -> GAME.cif
```

Important benchmarks include `closing_game.py` that models the Closing Game proposed in [1] for the closing phase of the [Bitcoin Lightning protocol](https://lightning.network/lightning-network-paper.pdf) as well as `routing_three.py`, which models the routing module of the Lightning protocol [1] for three users. There are also `closing_game-simplified.cif` and  `routing_game-simplified.cif`, that are simplified versions of the games mentioned before.

## Publications

[[1]](https://doi.org/10.48550/arXiv.2109.07429) Sophie Rain, Georgia Avarikioti, Laura Kovács, Matteo Maffei.
Towards a Game-Theoretic Security Analysis of Off-Chain Protocols (CSF 2022).

[[2]](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
Automating Security Analysis of Off-Chain Protocols (Talk at [FMBC 2022](https://fmbc.gitlab.io/2022/)).

[[3]](https://doi.org/10.34726/hss.2022.104340) Lea Salome Brugger.
Automating Proofs of Game-Theoretic Security Properties of Off-Chain Protocols (Diploma Thesis, 2022).

[[4]](https://dl.acm.org/doi/10.1145/3576915.3623183) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
CheckMate: Automated Game-Theoretic Security Reasoning (CCS 2023).
