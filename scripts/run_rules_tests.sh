#!/bin/bash
# Tests of the rules compiler (scripts/rules.mjs): the rules in examples/readable must give the same verdicts as
# the game trees next to them, tests/rules/*.rules must give tests/rules/*.game or fail with the message in their
# "# expect:" line. Usage (from the repo root): scripts/run_rules_tests.sh [path/to/checkmate]
CHECKMATE=$(realpath "${1:-build/checkmate}")
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
fail=0

verdicts() { "$CHECKMATE" "$1" | grep -E '^(Checking|YES|NO)'; }

for rules in examples/readable/*.rules; do
  name=$(basename "$rules" .rules)
  node scripts/rules.mjs "$rules" "$WORK/$name.game" || { echo "FAIL: $rules does not compile"; fail=1; continue; }
  verdicts "$WORK/$name.game" > "$WORK/$name.rules.out" || { echo "FAIL: checkmate on $rules"; fail=1; continue; }
  if [ -f "examples/readable/$name.game" ]; then
    verdicts "examples/readable/$name.game" > "$WORK/$name.game.out"
    if diff "$WORK/$name.game.out" "$WORK/$name.rules.out" >/dev/null; then echo "ok: $rules (as $name.game)"
    else echo "FAIL: $rules and $name.game give different verdicts"; diff "$WORK/$name.game.out" "$WORK/$name.rules.out"; fail=1; fi
  else
    echo "ok: $rules"
  fi
done

for rules in tests/rules/*.rules; do
  expect=$(sed -n '1s/^# expect: //p' "$rules")
  if [ -n "$expect" ]; then
    if node scripts/rules.mjs "$rules" > /dev/null 2> "$WORK/err"; then echo "FAIL: $rules compiles, expected: $expect"; fail=1
    elif grep -qF "$expect" "$WORK/err"; then echo "ok: $rules"
    else echo "FAIL: $rules: expected \"$expect\", got: $(cat "$WORK/err")"; fail=1; fi
  elif node scripts/rules.mjs "$rules" | diff "${rules%.rules}.game" - ; then echo "ok: $rules"
  else echo "FAIL: $rules does not give ${rules%.rules}.game (above: < expected, > actual)"; fail=1; fi
done
exit $fail
