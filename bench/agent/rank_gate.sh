#!/usr/bin/env bash
# rank_gate.sh — witness for the ArkLib premise selector (the premise-selection
# component of a proof agent). GREEN iff the contrastive energy model, trained on
# REAL mined ArkLib (statement -> used-premise) pairs, ranks the true premise on
# held-out theorems decisively above the random floor AND the untrained base. No
# inflated result — the criterion is relative to an identically-evaluated untrained
# model.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$(git -C "$HERE" rev-parse --show-toplevel)"
# Any python3 with torch installed. Override with ARKLIB_EBM_PY=/path/to/python.
PY="${ARKLIB_EBM_PY:-python3}"

# 1. mine the real pairs if absent
[ -s bench/agent/arklib_premises.jsonl ] || python3 bench/agent/mine_premises.py || {
  echo "RANK-GATE: RED — premise mining failed"; exit 1; }

# 2. train + held-out eval; the python exits 0 iff trained beats floor AND base
exec "$PY" bench/agent/rank_train_eval.py
