# CheckMate
CheckMate is a framework designed to automatically check security properties of games modeling off-chain (blockchain) protocols.
The framework analyzes the following properties:

* weak immunity
* weaker immunity
* collusion resilience
* practicality

The modeling of protocols as games and manual analysis of security properties can be found in [1].
This and other related materials are listed below.

The input for CheckMate is a JSON file representing a game.
Examples for such a JSON instance can be found in the `examples` folder.

## Prerequisites
In order to run CheckMate, you need Python >= 3.8 with the [`z3-solver` package](https://pypi.org/project/z3-solver/) installed.
To acquire the required packages, run `pip install -r requirements.txt` in this directory.

## Run
CheckMate provides two modes: `analyze` and `check`.
The subcommand `analyze` invokes the security analysis for the input game (provided as JSON file), whereas `check` is used to verify that a provided set of joint strategies for the input game indeed fulfill the security properties.

### Analysis
To run the security analysis, execute the following command (where `GAME` is the path to the input JSON - for example, `examples/closing_game.json`):
```
./checkmate GAME analyze
```

The analysis mode provides additional options:
* `--preconditions`: If a property is not satisfied, try to compute preconditions under which the property holds. By default, this option is set to `false`.
* `--counterexamples`: If a property is not fulfilled, provide counterexamples, i.e. "justifications" why the property does not hold (still experimental for practicality). By default, this option is set to `false`.
* `--properties {wi,weri,cr,pr} [{wi,weri,cr,pr} ...]`: Analyze a subset of the four security properties (`wi` stands for weak immunity, `weri` for weaker immunity, `cr` for collusion resilience and `pr` for practicality). By default, this option is set to `wi weri cr pr` (meaning that by default, all properties are analyzed).
* `--output`: Print a JSON encoding of the analysis result to the console. By default, this option is set to `false`.

For instance, to run a security analysis on the Closing Game [1] with counterexample generation, but without considering practicality, and save the output to a file `result.json`, execute the following command:
```
./checkmate examples/closing_game.json analyze --counterexamples --properties wi weri cr --output > result.json
```

### Verification
The `check` subcommand only takes one (required) parameter: the path to the file containing the JSON encoding of the joint strategies that should be checked.
Hence, to run the verification, execute the following command (where `STRATEGIES` is the path to the respective file):
```
./checkmate GAME check STRATEGIES
```

The output of CheckMate when running the analysis with the `--output` option adheres to the schema of the JSON instance that is expected from the `check` command.
For example, in order to check the strategies for the Closing Game [1] in `result.json` which were generated before, execute:
```
./checkmate examples/closing_game.json check result.json
```

You can print the usage of the two subcommands by executing the following command (with `MODE` being either `analyze` or `check`):
```
./checkmate GAME MODE --help
```

## Examples
All benchmarks can be found in the `examples` folder.
Most importantly, `closing_game.json` models the Closing Game proposed in [1] for the closing phase of the [Bitcoin Lightning protocol](https://lightning.network/lightning-network-paper.pdf) and `closing_game-simplified.json` a simplified version of the game.
The file `routing_game-simplified.json` contains the JSON representation of a simplified Routing Game [1], which models the routing module of the Lightning protocol.
The remaining JSON files contain (minimal) artificial games used for testing.

Additionally, the directory contains scripts for encoding input games in JSON format.
For example, `routing.py` can be used to generate JSONs for N-player Routing.

## Publications
[[1]](https://doi.org/10.48550/arXiv.2109.07429) Sophie Rain, Georgia Avarikioti, Laura Kovács, Matteo Maffei.
Towards a Game-Theoretic Security Analysis of Off-Chain Protocols (2022).

[[2]](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) Lea Salome Brugger, Laura Kovács, Anja Petković Komel, Sophie Rain, Michael Rawson.
Automating Security Analysis of Off-Chain Protocols (Talk at [FMBC 2022](https://fmbc.gitlab.io/2022/)).

[[3]](https://doi.org/10.34726/hss.2022.104340) Lea Salome Brugger.
Automating Proofs of Game-Theoretic Security Properties of Off-Chain Protocols (Diploma Thesis, 2022).