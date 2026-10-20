#!/bin/bash
# Run checkmate with several flag sets on tests/regressions/*.json and verify each result,
# and --subtree on tests/regressions/subtree_mode/*.json.
# Usage (from the repo root): scripts/run_regressions.sh [path/to/checkmate]

CHECKMATE=${1:-build/checkmate}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
FLAG_SETS=(
  ""
  "--strategies --counterexamples"
  "--strategies --counterexamples --all_cases"
  "--counterexamples --all_counterexamples --all_cases"
  "--strategies --counterexamples --all_cases --no-cr-node-cache --no-cr-leaf-cache --no-cr-implied-groups --no-cr-violated-lookup --no-problematic-groups --exact-splits --reset-from-root"
)
fail=0
for game in tests/regressions/*.json; do
  for flags in "${FLAG_SETS[@]}"; do
    complete=""
    [[ $flags == *--all_cases* ]] && complete="--complete-cases"
    # shellcheck disable=SC2086
    if ! "$CHECKMATE" "$game" $flags --json-out "$OUT/r.json" > "$OUT/log" 2>&1; then
      echo "FAIL: $CHECKMATE $game $flags crashed"; tail -20 "$OUT/log"; fail=1; continue
    fi
    if ! python3 scripts/check_result.py "$game" "$OUT/r.json" $complete > "$OUT/check" 2>&1; then
      echo "FAIL: $CHECKMATE $game $flags"; cat "$OUT/check"; fail=1; continue
    fi
    echo "ok: $game $flags"
  done
done
# --subtree writes <input>.out next to the input, so run on copies
for game in tests/regressions/subtree_mode/*.json; do
  cp "$game" "$OUT/sub.json"
  if ! "$CHECKMATE" "$OUT/sub.json" --subtree --json-out "$OUT/r.json" > "$OUT/log" 2>&1; then
    echo "FAIL: $CHECKMATE $game --subtree crashed"; tail -20 "$OUT/log"; fail=1; continue
  fi
  if ! python3 scripts/check_result.py --subtree "$game" "$OUT/r.json" > "$OUT/check" 2>&1; then
    echo "FAIL: $CHECKMATE $game --subtree"; cat "$OUT/check"; fail=1; continue
  fi
  echo "ok: $game --subtree"
done
exit $fail
