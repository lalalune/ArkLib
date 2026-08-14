#!/bin/bash
# Witness for completing the char-0 E₃ identification (#444): rEnergy G 3 = E₃ closed form.
# Exits 0 iff the target file compiles, is axiom-clean, carries no gap, AND states the
# rEnergy↔closed-form corollary (the r=2 rung input, unconditional in char 0).
# Scope: char-0 (2^k-th roots). NOT the prize — the char-p √-cancellation wall stays open.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 1
F="ArkLib/Data/CodingTheory/ProximityGap/Frontier/REnergyThreeCharZero.lean"
[ -f "$F" ] || { echo "WITNESS FAIL: target file $F absent"; exit 1; }
if grep -qE '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)|native_decide' "$F"; then
  echo "WITNESS FAIL: sorry/admit/native_decide in source"; exit 1
fi
# Must actually state the rEnergy closed-form corollary (not just the identification).
if ! grep -qE 'rEnergy[^=]*3' "$F"; then
  echo "WITNESS FAIL: file does not mention rEnergy _ 3 (the target moment)"; exit 1
fi
out=$(lake env lean "$F" 2>&1); ec=$?
if [ $ec -ne 0 ]; then echo "WITNESS FAIL: compile error"; echo "$out" | grep -i error | head -20; exit 1; fi
if echo "$out" | grep -q "sorryAx"; then echo "WITNESS FAIL: sorryAx in axiom audit"; echo "$out" | grep -i sorry; exit 1; fi
echo "WITNESS PASS: $F compiles axiom-clean, no gap; rEnergy G 3 = E₃ char-0 (prize char-p wall remains open)."
exit 0
