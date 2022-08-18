# CheckMate

CheckMate is a framework designed to automatically check security properties of games that arise from off-chain (blockchain) protocols. The framework yields a strategy (if it exists) for the following properties:

* weak immunity
* collusion resilience
* practicality.

The modeling of protocols as games and manual analysis of security properties can be found in the paper [here](https://arxiv.org/abs/2109.07429).

A short description of the framework was [presented](https://easychair.org/smart-program/FLoC2022/FMBC-2022-08-11.html#talk:201081) at FMBC 2022.

## How to run the code

Examples of games can be found in `./examples`.
To check security properties of the closing game, run the following code:

```
./checkmate examples/closing_game.json
```

To ouput the strategies as well add the `--output-strategies` flag:

```
./checkmate examples/closing_game.json --output-strategies
```

A minimal example can be found in `examples/market_entry_game-constants.json`
