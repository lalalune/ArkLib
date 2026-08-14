#!/bin/bash
# Runnable witness for the char-0 E₃-exact strata producer brick (#444).
# Exits 0 iff the target brick compiles AND is axiom-clean AND carries no sorry.
# Scope: char-0 producer of the r=2 rung — NOT the prize (char-p √-cancellation wall stays open).
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 1
F="ArkLib/Data/CodingTheory/ProximityGap/Frontier/E3StrataCharZero.lean"
[ -f "$F" ] || { echo "WITNESS FAIL: target file $F absent"; exit 1; }
if grep -qE '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)|native_decide' "$F"; then
  echo "WITNESS FAIL: sorry/admit/native_decide in source"; exit 1
fi
out=$(lake env lean "$F" 2>&1); ec=$?
if [ $ec -ne 0 ]; then echo "WITNESS FAIL: compile error"; echo "$out" | grep -i error | head -20; exit 1; fi
if echo "$out" | grep -q "sorryAx"; then echo "WITNESS FAIL: sorryAx in axiom audit"; echo "$out" | grep -i sorry; exit 1; fi
echo "WITNESS PASS: $F compiles axiom-clean, no sorry (char-0 E₃ producer; prize char-p wall remains open)."
exit 0
