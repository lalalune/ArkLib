"""Probe the graded-M dilation-pencil cardinality core (#444/#407, LEVER K generalized).

Setup (the combinatorial heart of Kelley-Owen Lemma 2.3 at general autocorrelation M):
  r blocks B_0..B_{r-1}, each of size r, ALL containing a common point p, pairwise
  intersections of card <= M (and >= 1, since all contain p). This is what the dilation
  pencil produces when the root set S has multiplicative autocorrelation <= M (so distinct
  pencil pairs overlap in <= M points, pencil_overlap_le_of_autocorr already proven), with
  M=1 the trinomial face (pencil_card_core, proven) and M=n/2 the coset-core wall
  (autocorr_ge_coset_core, proven).

Candidate graded core (extends pencil_card_core's r(r-1)+1 <= n to general M):
  CORE-A:    r*(r-1) + 1 <= M*(|union|)         -- so |union| >= (r(r-1)+1)/M
  Combined with |union| <= n  =>  r*(r-1) + 1 <= M*n  (the M-graded root-count bound)
  JOHNSON:   (r-1)^2 < M*n   (Stepanov sqrt(M*n) bound; M=1 recovers (r-1)^2<n)

We test CORE-A and JOHNSON against the MINIMUM feasible union over random admissible
block families (the adversary minimizes the union to stress the lower bound). Never n=q-1.
"""
import random

def min_feasible_union(r, M, n, trials=20000):
    worst = n + 1
    for _ in range(trials):
        blocks = []
        ok = True
        for _i in range(r):
            others = random.sample(range(1, n), r - 1)
            b = set([0] + others)
            good = True
            for pb in blocks:
                if len(b & pb) > M:
                    good = False
                    break
            if not good:
                ok = False
                break
            blocks.append(b)
        if not ok:
            continue
        U = set()
        for b in blocks:
            U |= b
        worst = min(worst, len(U))
    return worst

cases = [(4, 1, 16), (4, 2, 16), (5, 2, 16), (4, 2, 12), (6, 2, 32),
         (5, 3, 16), (8, 3, 64), (3, 2, 8), (7, 2, 32), (5, 1, 32)]
allpass = True
for (r, M, n) in cases:
    wu = min_feasible_union(r, M, n)
    A = r * (r - 1) + 1
    coreA = (A <= M * wu)
    rootbound = (A <= M * n)
    J = (r - 1) * (r - 1)
    john = (J < M * n)
    ok = coreA and rootbound and john
    allpass = allpass and ok
    print(f"r={r:2d} M={M} n={n:3d}: minUnion={wu:3d} | "
          f"CORE-A r(r-1)+1={A} <= M*union={M*wu}? {coreA} | "
          f"root r(r-1)+1 <= M*n={M*n}? {rootbound} | "
          f"Johnson (r-1)^2={J} < M*n? {john}")
print("VERDICT:", "PASS" if allpass else "FAIL")
