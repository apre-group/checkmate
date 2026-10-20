#!/bin/bash
# tmux session with one fuzz.py per window; a window that finds a bug stops there for debugging.
# Usage (from the repo root): scripts/fuzz_session.sh [--num WINDOWS] [fuzz.py options]

SESSION="fuzzing checkmate"
DIR="$(pwd)"
NUM_WINDOWS=10

if [ "$1" = "--num" ]; then
  if [ -z "$2" ] || ! [[ "$2" =~ ^[0-9]+$ ]]; then
    echo "Error: --num requires a positive integer argument"
    exit 1
  fi
  NUM_WINDOWS=$2
  shift 2
fi

CMD="scripts/fuzz.py $*"

if tmux has-session -t "$SESSION" 2>/dev/null; then
  echo "Session '$SESSION' already exists, attaching..."
  tmux attach -t "$SESSION"
  exit 0
fi

tmux new-session -d -s "$SESSION" -c "$DIR" -n "fuzz-1"
tmux send-keys -t "$SESSION:fuzz-1" "$CMD" Enter
for i in $(seq 2 "$NUM_WINDOWS"); do
  tmux new-window -t "$SESSION" -c "$DIR" -n "fuzz-$i"
  tmux send-keys -t "$SESSION:fuzz-$i" "$CMD" Enter
done

tmux select-window -t "$SESSION:fuzz-1"
tmux attach -t "$SESSION"
