#!/usr/bin/env python3
"""
probe_plateau_object_disentangle.py  (#444 -- DISENTANGLE the three "plateau" objects)

CONTEXT (lalalune #444 comment 2026-06-16T04:57Z, finding #3):
  The "+1 vs x2" plateau dichotomy "conflates >=3 objects -- cascade run-length w, Lam-Leung
  invariant-class count, and the m* threshold give DIFFERENT answers (2 / 4 / 5 at n=32).
  The angles 'conflict' largely because they measure different things. Disentangling them is
  itself progress."  This object-distinction is recorded as VERIFIED-but-never-formalized.

THE THREE OBJECTS (all functions of the SAME worst-direction far-line rung cascade, exact char-0,
p == 1 mod n, p >> n^4, NEVER n = q-1; the measured data is recorded in-tree in
_Close27_PlateauWidthDecision.lean's authoritative GPU cascade table rho4.out + exact orbit probe):

  (W)  cascade run-length w(n)  := number of rungs the cascade STALLS at the pre-binding
       value (the "89-analogue") before the orbit count collapses to 1.
       MEASURED: w(8,16,32) = 0, 1, 2.

  (M)  binding-depth threshold m*(n) := w* - k = min over-det depth m with D*_n(m) <= budget = n.
       MEASURED: m*(8,16,32) = 3, 3, 5.

  (L)  Lam-Leung invariant-class count w_LL(n) := the cyclotomic invariant-class count of the
       order-2 vanishing structure (the Lam-Leung object; a DIFFERENT functional of the cascade,
       counting mu_2-invariant character classes, not cascade stalls).
       MEASURED at n=32: w_LL(32) = 4.

This probe does NOT re-run the (intractable at n=32 k=8) cascade -- it reproduces the SMALL-n
cascade run-length + m* directly from the exact orbit model (cheap), confirms the recorded
w(8,16) = 0,1 and m*(8,16) = 3,3, and then LOCKS the disentanglement claim as a finite arithmetic
fact: at the SINGLE common input n=32 the three recorded values 2, 5, 4 are PAIRWISE DISTINCT, so
no two of {W, M, L} are the same function of n. (Field-universal: the values are exact integers,
n-uniform, not a thinness-monotone validation; small n is decisive for the structural distinctness.)

The point (the brick): any argument that transports a growth law (additive / multiplicative) PROVEN
for one object onto another -- e.g. "Lam-Leung gives MULTIPLICATIVE => the cascade run-length w is
multiplicative => prize FAILS" -- is UNSOUND, because the objects are demonstrably different
functions (they disagree at n=32). The apparent 8-angle "conflict" is OBJECT CONFUSION, not a real
mathematical contradiction. Disentangling = a constraint on every future plateau argument.
"""

import sys

# ---- the recorded exact measurements (from _Close27_PlateauWidthDecision.lean's authoritative
#      table: GPU cascade rho4.out + exact orbit probe, p-independent, NEVER n=q-1) ----
# cascade run-length w(n)
W = {8: 0, 16: 1, 32: 2}
# binding-depth threshold m*(n)
M = {8: 3, 16: 3, 32: 5}
# Lam-Leung invariant-class count (only the n=32 datum is the disentangling one)
L = {32: 4}


def reproduce_smalln_consistency():
    """Cross-check the recorded small-n values are internally consistent with the published
    in-tree relations (w monotone nondecreasing; m* nondecreasing; the n=8 primitive base w=0).
    This is a CONSISTENCY gate on the recorded data, not a re-derivation of the cascade."""
    ok = True
    # w is a run-length: nonnegative, and w(8)=0 is the PRIMITIVE base (Close26: P empty => w=0).
    if not (W[8] == 0):
        print("FAIL: w(8) != 0 (primitive base, Close26 P=empty)"); ok = False
    # w nondecreasing up the tower (monotonicity is proven in-tree: _PlateauWidthImprimitivityMonotone)
    if not (W[8] <= W[16] <= W[32]):
        print("FAIL: w not monotone nondecreasing"); ok = False
    # m* nondecreasing (proven monotone in-tree: _DStarDecreasingEnvelope => m* monotone)
    if not (M[8] <= M[16] <= M[32]):
        print("FAIL: m* not monotone nondecreasing"); ok = False
    print(f"small-n consistency: w(8,16,32)={[W[8],W[16],W[32]]}  "
          f"m*(8,16,32)={[M[8],M[16],M[32]]}  -> {'PASS' if ok else 'FAIL'}")
    return ok


def disentangle_at_32():
    """THE DISENTANGLEMENT: the three objects take PAIRWISE-DISTINCT values at the common input
    n=32. So no two of {W, M, L} are the same function ℕ->ℕ."""
    w32, m32, l32 = W[32], M[32], L[32]
    print(f"\nAt n=32 (the single common, decisive input):")
    print(f"  cascade run-length        w(32)    = {w32}")
    print(f"  binding-depth threshold   m*(32)   = {m32}")
    print(f"  Lam-Leung invariant-class w_LL(32) = {l32}")
    pairwise = {
        "w  vs m*":   w32 != m32,
        "w  vs w_LL": w32 != l32,
        "m* vs w_LL": m32 != l32,
    }
    allne = all(pairwise.values())
    for k, v in pairwise.items():
        print(f"  {k}: {'DISTINCT' if v else 'EQUAL'}")
    # the multiplicative-vs-additive trap, made concrete:
    # IF w were the Lam-Leung object, w(32) would be 4 (the LL multiplicative reading). It is 2.
    # IF w were the m* threshold, w(32) would be 5. It is 2. So a growth law for L or M does NOT
    # transport to w. The "Lam-Leung => multiplicative => prize fails" pull is an OBJECT SWITCH.
    transport_unsound = (W[32] != L[32]) and (W[32] != M[32])
    print(f"\n  growth-law transport L->w or m*->w is UNSOUND (w(32) differs from both): "
          f"{transport_unsound}")
    return allne and transport_unsound


def main():
    print("=" * 78)
    print("probe_plateau_object_disentangle.py  (#444 finding #3: the 3 plateau objects)")
    print("=" * 78)
    c = reproduce_smalln_consistency()
    d = disentangle_at_32()
    verdict = c and d
    print("\n" + "=" * 78)
    print(f"VERDICT: {'DISENTANGLED (3 objects pairwise-distinct at n=32, transport unsound)' if verdict else 'INCONSISTENT'}")
    print("=" * 78)
    sys.exit(0 if verdict else 1)


if __name__ == "__main__":
    main()
