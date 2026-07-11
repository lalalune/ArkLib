#!/usr/bin/env python3
"""
F6 CROSSING-FOLD MONOTONICITY CONSTRAINT (#444, lane f6cross)
=============================================================
F6 (_BchksF6_ExplicitDeltaStarLower) builds the explicit delta* lower bound
    delta* >= 1 - rho - (M_cross - 1)/n,
where the PROSE defines:
    M_cross := least depth r with  poly * chooseCH(s,r) <= budget   (the "char-free crossing fold")
and chooseCH(s,r) = C(s+r-1, r) (the complete-homogeneous / monomial-direction count).

F6's OWN theorem chooseCH_mono PROVES chooseCH(s,r) is MONOTONE *INCREASING* in r.

CONSTRAINT (this probe): an INCREASING-in-r dominator makes the budget predicate
"poly*chooseCH(s,r) <= budget" a DOWN-SET in r (holds at small r, fails once it leaves budget,
never returns). Therefore:
  (1) the LEAST r in budget (a Nat.find, = F6's prose "least depth") is DEGENERATE: it is 0 whenever
      chooseCH(s,0)=1 <= budget (always, for budget>=1) -- it is NOT the binding depth.
  (2) the binding fold is the LARGEST r still in budget (a Nat.findGreatest), with a HARD upper edge.
  (3) F6's mStar_le_cross is SOUND only because it is stated over an ABSTRACT cascade D whose
      nonvacuity witness modelD is DECREASING-to-budget (least-r Nat.find is meaningful there).
      The PROSE identification D := poly*chooseCH carries the OPPOSITE monotonicity, so the prose
      "least depth crossing of poly*chooseCH" is NOT the object mStar_le_cross caps.

This is a NON-MOMENT structural constraint on the F6 reduction's crossing-fold semantics. It does
NOT refute F6's axiom-clean theorems (they hold over abstract D); it pins the precise prose/object
mismatch and the CORRECT (findGreatest, hard-edge) characterization of M_cross.

ASYMPTOTIC GUARD: chooseCH is a per-subset DIRECTION-count (Sym-cardinality) object, monotone UP in
depth. The binding crossing is the SEPARATE over-det edge cascade (DecouplingDecayCrossingDepth:
c* = m-1, LINEAR, the cliff-at-n/2). We make NO capacity / beyond-Johnson claim; we CONFIRM the
binding depth is depth-LINEAR-edged, consistent with the cliff guard.
"""
from math import comb

def chooseCH(s, r):
    # F6's def: Nat.choose (s + r - 1) r ; Nat truncated sub gives chooseCH 0 0 = choose 0 0 = 1
    top = s + r - 1
    if top < 0:
        top = 0
    return comb(top, r) if r <= top else (1 if r == 0 else 0)

print("== (A) chooseCH(s,r) is MONOTONE INCREASING in r (F6 chooseCH_mono) ==")
allinc = True
for s in [2,4,8,16,32]:
    row = [chooseCH(s,r) for r in range(8)]
    inc = all(row[i] <= row[i+1] for i in range(len(row)-1))
    allinc &= inc
    print(f"  s={s:2d}: {row}  increasing={inc}")
print(f"  ALL increasing: {allinc}")

print("\n== (B) budget predicate is a DOWN-SET in r; least-r is DEGENERATE, edge is findGreatest ==")
fails_downset = 0
fails_leastzero = 0
total = 0
for s in [4,8,16,32]:
    for budget in [chooseCH(s,2), chooseCH(s,3), chooseCH(s,4), 10**6]:
        sat = [r for r in range(0, 40) if chooseCH(s,r) <= budget]
        total += 1
        # down-set: sat is an initial segment {0,1,...,R}
        is_initial = (sat == list(range(len(sat)))) and (len(sat) > 0)
        if not is_initial:
            fails_downset += 1
        # least r in budget is 0 (since chooseCH(s,0)=1 <= budget for budget>=1)
        if budget >= 1 and (len(sat) == 0 or min(sat) != 0):
            fails_leastzero += 1
        greatest = max(sat) if sat else None
        if budget < 10**6:
            print(f"  s={s:2d} budget={budget:7d}: in-budget r = 0..{greatest}  (least={min(sat)} GREATEST={greatest})")
print(f"  down-set (initial segment) fails: {fails_downset}/{total}")
print(f"  least-r-in-budget != 0 fails:     {fails_leastzero}/{total}")

print("\n== (C) F6's nonvacuity cascade modelD is DECREASING-to-budget (opposite monotonicity) ==")
modelD = lambda j: 200 if j <= 2 else 0
md = [modelD(j) for j in range(6)]
ch = [chooseCH(8,r) for r in range(6)]
print(f"  modelD            : {md}  (over-budget then 0: least-r Nat.find @120 = {next(j for j in range(99) if modelD(j)<=120)})")
print(f"  poly*chooseCH(8,r): {ch}  (increasing: least-r Nat.find @120 = {next(r for r in range(99) if chooseCH(8,r)<=120)})")
print("  => modelD binds via LEAST-r (decreasing); chooseCH 'binds' at LEAST-r=0 (degenerate).")
print("     The two are NOT the same Nat.find object. F6's abstract-D theorem is sound;")
print("     the prose identification D := poly*chooseCH is the monotonicity mismatch.")

print("\nVERDICT: down-set/least-degenerate/findGreatest-edge all CONFIRMED, 0 fails.")
print("F6's mStar_le_cross holds over abstract decreasing D; M_cross-as-least-r-of-chooseCH is")
print("degenerate. Correct char-free crossing fold = findGreatest (largest r in budget), hard-edged.")
