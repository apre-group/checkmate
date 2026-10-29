# Fuzzing CheckMate

`scripts/fuzz.py` tests CheckMate on random games, both ordinary games (EFGs) and conditional games (CEFGs, see the [README](README.md#conditional-games-cefgs)). It runs CheckMate on each game, then checks every answer independently: a separate checker verifies the results, and the verdicts must not change when the flags, the optimizations or the game itself change in ways that cannot affect them.

## Quick start

Build CheckMate as described in the [README](README.md#build), then run from the repository root:

```shell
scripts/fuzz.py --num 100                 # 100 random games, EFGs and CEFGs
scripts/fuzz.py --games cefg              # only CEFGs, until it finds a bug
scripts/run_regressions.sh                # rerun the games of previously fixed bugs
```

You also need Python 3 with the Z3 bindings (`pip install z3-solver`), which the generator and the checker use.

The fuzzer writes its games to `out/` and deletes them when an iteration passes. It stops at the first bug, prints it and keeps the game files.

## Running in parallel

Each run picks its own random seeds, so several runs can work at the same time without testing the same games:

```shell
scripts/fuzz_session.sh --num 10 --num 100 --quiet
```

This opens a [tmux](https://github.com/tmux/tmux) session called `fuzzing checkmate` with one fuzzer per window. The first `--num` is the number of windows (default 10); all later options go to `fuzz.py`. A window that finds a bug stops there, so you can look at it. Switch windows with `Ctrl-b n` / `Ctrl-b p`, list them with `Ctrl-b w`, detach with `Ctrl-b d`, and end the session with `tmux kill-session -t "fuzzing checkmate"`. Running the script again while the session exists reattaches to it.

Without tmux, give each run its own log file, since their output would otherwise be mixed on one terminal:

```shell
seq 10 | xargs -P10 -I{} sh -c 'scripts/fuzz.py --num 100 > out/fuzz_{}.log 2>&1'
```

## Options

| Option | Meaning |
|---|---|
| `--num N`, `-n N` | Number of iterations. Default: run until a bug is found. |
| `--games efg\|cefg\|both` | Which games to fuzz: EFGs, CEFGs, or both (default; the seed decides which). |
| `--seed S` | Use seed `S` for every iteration, to reproduce a bug. Combine it with `--num 1`. |
| `--quiet`, `-q` | Print only the seed of each iteration, the statistics and bugs. When an iteration finds a bug, its full output is printed too. |
| `--stats-every N` | Print statistics every `N` iterations (default 10). |
| `--tout T`, `-t T` | Timeout in seconds per CheckMate call (default 20). Timeouts are skipped and counted. |
| `--check-tout T` | Timeout in seconds per checker call (default 20). |
| `--checkmate PATH` | The CheckMate binary (default `build/checkmate`). |
| `--js-gen` | Generate the EFGs with the web page's generator, `html/gen_game.js`. |

## What each iteration checks

### EFGs

For each random game, the fuzzer runs CheckMate:

1. without flags;
2. with `--strategies --counterexamples`, sometimes with `--all_cases`;
3. with random flags, including the testing-only switches that turn off optimizations (`--no-cr-node-cache`, `--exact-splits`, …; see the [README](README.md#run)).

Each run writes `--json-out` results, which `scripts/check_result.py` verifies. The checker uses its own reading of the semantics in the README, not CheckMate's code:

- **Cases:** each case is satisfiable, and its verdict agrees with a direct SMT encoding of the property. With `--all_cases`, the cases together cover all the constraints.
- **Strategies:** for a YES verdict, the strategies are legal moves and actually secure.
- **Counterexamples:** for a NO verdict, the counterexamples are legal moves and actually violate the property. For practicality, every subgame-perfect outcome after the deviation must be better for the deviating player.
- **Weakest preconditions** from `--preconditions`.

The verdicts must also agree:

- across all the flag combinations above;
- after transforms that cannot change them: renaming players (which changes their order), permuting children, renaming actions or constants, scaling or shifting utilities;
- when a random subtree is analyzed separately with `--subtree` and spliced into the rest of the game (the supertree), sometimes with a second subtree nested inside the first. The subtree results are also checked directly.

### CEFGs

`scripts/gen_cefg.py` generates conditional games: known and unknown constants, condition nodes that reveal unknowns (or split on known constants), and honest histories that continue in every condition. The unknowns usually take a few values only (an initial constraint `u0 = 0 | u0 = 2`), otherwise they are real. Some games have only an honest utility, as for a subtree off the honest history.

About a third of the CEFGs are EFGs embedded into a CEFG: the EFG gets condition nodes with a copy of the same subtree below every condition, deep in the tree on known constants, and at the root revealing constants that are now unknown. This cannot change any verdict, so the CEFG analysis must agree with the EFG analysis of the original game, which `check_result.py` verifies. This is the only independent check of CEFG verdicts; everything else compares CheckMate with itself.

About one in ten condition nodes on an unknown gets overlapping conditions (`u0 >= 1` and `u0 <= 1`), and about one in ten a gap (`u0 > 1` and `u0 < 1`, or a partition of the finite domain that leaves out a value). CheckMate must reject such a game with an error about the overlap or the gap, unless the constraints and the conditions on the way to the node make it unreachable; the other games must pass these checks. The analysis of a game with such conditions then runs with `--no_validate_conditions`. A subtree cut for the compositional check gets the conditions on the way to it as additional initial constraints, and is only cut where these conditions can hold.

The verdicts of a CEFG come from its `--json-out` result, which has the verdicts only (CEFGs have no strategies, counterexamples or cases yet). For each game, the fuzzer checks that:

- CheckMate analyses it as a CEFG, with one verdict per property for every honest history and honest utility, and, under the index of each honest history (`honest_history`), that honest history (conditions are not compared, CheckMate writes them in its own syntax);
- the text output has the same verdicts as `--json-out`, and an undecided verdict (`"holds": null`) is for practicality and has a reason;
- with `--subtree`, `--json-out` has the same result as `SUBTREE.out`;
- the verdicts do not change with a subset of the properties, with the options that CEFGs ignore (`--counterexamples`, `--all_cases`, the testing switches, …), after the transforms above (which also permute conditions and rename unknowns), and when a random subtree is analyzed separately with `--subtree` and spliced into the supertree, sometimes nested.

Verdicts that are `UNKNOWN` (practicality that neither Z3 nor cvc5 decided) are not compared.

## When it finds a bug

The fuzzer prints a red block with:

- `BUG:` and what went wrong;
- `Command was:`, the command that failed;
- the end of its output, if it printed any;
- `Game kept in ...`, the game file and the other files of this iteration;
- `REPRODUCE with: scripts/fuzz.py --seed N --num 1`.

To work on it:

1. Rerun the `REPRODUCE` command. The same seed generates the same game and the same flags, so the bug comes back without any of the other games.
2. Run the command from `Command was:` directly on the kept game. Long CheckMate output is cut in the bug report; all of it is in `out/fuzzTest_N-failure.txt`.
3. After the fix, add the game to `tests/regressions/` (to `tests/regressions/subtree_mode/` if it has to be analyzed with `--subtree`). `scripts/run_regressions.sh` runs CheckMate on every game there with several flag sets and verifies each result.

The checkers can also be run by themselves on any game and result:

```shell
build/checkmate game.json --strategies --counterexamples --json-out result.json
scripts/check_result.py game.json result.json            # add --complete-cases after --all_cases
```

They exit with 0 if the result is correct, 1 if it is wrong, and 2 if they could not decide (solver timeout).

## Statistics

Every `--stats-every` iterations, and at the end, the fuzzer prints what it has covered so far:

```
=== Statistics after 80 iterations ===
  EFGs: 41 games
  players: 2 23, 3 29, 4 12, 5 12, 6 4
  leaves: 1-3 26, 4-8 30, 9-16 14, 17-32 7, 33+ 3
  depth: 1 13, 2 11, 3 22, 4 18, 5 12, 6 4
  honest history length: 1 15, 2 14, 3 17, 4 21, 5 10, 6 3
  games: with infinitesimals in utilities 36, with repeated leaves 34, weak != weaker 9
  weak_immunity         YES  37%, split  22%, mixed  22% of 108 runs, most cases 3
  ...
  subtrees: cut along honest 28, cut off honest 39, cut nested 7
  transforms: permute_children 33, rename_actions 26, ...
  switches: --exact-splits 125, --no-cr-implied-groups 107, ...
  verified: game 237, transformed 80, subtree 74, supertree 67, strategies 255, counterexamples 1186, preconditions 164
  skipped: checker timeouts 3
```

- **players, leaves, depth, honest history length:** how many games had each size.
- **games:** how many games had infinitesimals in their utilities, two leaves with the same utilities, or different verdicts for weak and weaker immunity.
- **per property:** how often it holds (YES), how often the analysis split into several cases (split), and how often some cases hold and others don't (mixed); "most cases" is the largest number of cases in one result.
- **subtrees:** where the subtree for the compositional check was cut: on the honest history, off it, or nested.
- **transforms, switches:** how often each was used.
- **verified:** how many results the checker accepted, and how many strategies, counterexamples and preconditions they contained.
- **skipped:** results that timed out or that the checker could not decide or does not support.

For CEFGs, a second block follows:

```
  CEFGs: 39 games, 12 of them embedded EFGs
  players: 2 19, 3 15, 4 5
  leaves: 1-3 4, 4-8 21, 9-16 11, 17-32 3
  unknowns: 0 5, 1 18, 2 16
  condition nodes: 0 2, 1 14, 2-3 15, 4-6 8
  games: with revealing condition nodes 27, honest through conditions 25, honest utility only 4
  weak_immunity         YES  41%, NO  58%, UNKNOWN   0% of 44 runs
  ...
  conditions: rejected overlap 3, rejected gap 4, defect unreachable 2
  subtrees: cut along honest 15, cut off honest 18, cut nested 9
  transforms: permute_children 14, rename_symbols 12, ...
  compared: with EFG 12, options 35, transformed 37, supertree 30
```

- **unknowns, condition nodes:** how many games had each number of unknown constants and of condition nodes.
- **games:** how many games had condition nodes revealing unknowns, honest histories through condition nodes, or only an honest utility.
- **per property:** how often the verdict was YES, NO or UNKNOWN.
- **conditions:** how many games with overlapping conditions or a gap CheckMate rejected, and how many it accepted because the constraints make the defect unreachable.
- **compared:** how often the verdicts were compared with the EFG analysis of an embedded EFG, with other options, after transforms and with a supertree.

If a number stays at zero, that part of CheckMate is not being tested, and the generator in `scripts/gen_game.py` may need tuning. `scripts/gen_stats.py --num 500` measures the generated games without the checker, so you can compare generator changes quickly.

## Sanitizer builds

To catch memory errors and undefined behavior, fuzz an AddressSanitizer and UndefinedBehaviorSanitizer build:

```shell
cmake -B build-asan -DCMAKE_BUILD_TYPE=Debug -DSANITIZE=ON
cmake --build build-asan
scripts/fuzz.py --checkmate build-asan/checkmate
```

The fuzzer sets the sanitizer options itself, so a sanitizer report stops CheckMate and counts as a crash.

## The scripts

| File | Purpose |
|---|---|
| `scripts/fuzz.py` | The fuzzer. |
| `scripts/fuzz_session.sh` | Runs several fuzzers in a tmux session. |
| `scripts/gen_game.py` | Generates random games (`scripts/gen_game.py --seed S -o game.json` writes one). |
| `scripts/gen_cefg.py` | Generates random CEFGs (`--embed`: an EFG embedded into a CEFG), and has the helpers for walking them. |
| `scripts/check_result.py` | Checks a `--json-out` result independently of CheckMate. |
| `scripts/transform.py` | Transforms that must not change the verdicts. |
| `scripts/compose.py` | Splits a game into a subtree and a supertree for the `--subtree` check. |
| `scripts/gen_stats.py` | Statistics on generated games, for tuning the generator. |
| `scripts/run_regressions.sh` | Checks the games in `tests/regressions/`. |
| `scripts/lsan.supp` | Leak reports to ignore in sanitizer builds. |
