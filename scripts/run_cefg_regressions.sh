#!/bin/bash
# Run checkmate on the CEFG examples in examples/conditional_actions (games with condition nodes) and on the games
# in tests/cefg_conditions (checks of the conditions), and compare the
# analysed histories and verdicts with tests/cefg_regressions/expected.txt.
# Usage (from the repo root): scripts/run_cefg_regressions.sh [path/to/checkmate] [--update]
# sign-2 and mixed-2 need cvc5 (on the PATH or in CHECKMATE_CVC5); --update rewrites the expected results.

CHECKMATE=$(realpath "${1:-build/checkmate}")
EXPECTED=tests/cefg_regressions/expected.txt
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# generate the games from the DSL scripts, in a copy so that nothing is written to the repo
mkdir -p "$WORK/conditional_actions"
cp examples/dsl.py "$WORK/"
cp examples/conditional_actions/*.py "$WORK/conditional_actions/"
for script in "$WORK"/conditional_actions/*.py; do
  # most scripts print the game, unknown-quantifier.py writes its variants next to itself
  python3 "$script" > "${script%.py}.json" || { echo "FAIL: $script"; exit 1; }
  [ -s "${script%.py}.json" ] || rm "${script%.py}.json"
done

{
  for game in "$WORK"/conditional_actions/*.json; do
    echo "== $(basename "$game")"
    (cd "$WORK/conditional_actions" && "$CHECKMATE" "$(basename "$game")" 2>&1) | grep -E '^(Checking|YES|NO|UNKNOWN|checkmate:)'
  done
  # the checks of the conditions (overlaps, gaps, conditions that cannot hold); *-unchecked.json without them
  mkdir -p "$WORK/cefg_conditions"
  cp tests/cefg_conditions/*.json "$WORK/cefg_conditions/"
  for game in "$WORK"/cefg_conditions/*.json; do
    flags=()
    case "$game" in *-unchecked.json) flags=(--no_validate_conditions);; esac
    echo "== cefg_conditions/$(basename "$game")"
    (cd "$WORK/cefg_conditions" && "$CHECKMATE" "$(basename "$game")" "${flags[@]}" 2>&1) | grep -E '^(Checking|YES|NO|UNKNOWN|checkmate:)'
  done
} > "$WORK/actual.txt"

if [ "$2" == "--update" ]; then
  mkdir -p "$(dirname "$EXPECTED")"
  cp "$WORK/actual.txt" "$EXPECTED"
  echo "updated $EXPECTED"
elif diff "$EXPECTED" "$WORK/actual.txt"; then
  echo "ok: $(grep -c '^==' "$EXPECTED") CEFG examples"
else
  echo "FAIL: results differ from $EXPECTED (above: < expected, > actual)"
  exit 1
fi
