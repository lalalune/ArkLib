#!/usr/bin/env python3
"""
Door-IV Lane-1 probe (#444 / #464): is the worst-b coherence+bounded-imbalance picture
PARTITION-DEPTH-INVARIANT? (index-4 split, genuinely new — extends the index-2 stationary band.)

Established (c1aae3d7e + [doorIV-worstb-imbalance-stationary-band]):
  at the worst frequency b*, the INDEX-2 split μ_n = μ_{n/2} ∪ h·μ_{n/2} into halves A,B is
  PHASE-COHERENT (rho=1, angle=0, M=‖A‖+‖B‖) with a STATIONARY bounded imbalance r=min/max ≈0.83.

THIS PROBE: take the INDEX-4 split μ_n = ⊔_{j=0..3} g^j·μ_{n/4} into four equal coset-quarters
Q0,Q1,Q2,Q3 (n a multiple of 4, n=2^a). At the TRUE worst frequency b* (full coset scan), measure:
  - quarter COHERENCE: is M(b*) = Σ_j ‖Q_j(b*)‖  (all four quarters phase-aligned, rho4=1)?
    i.e. rho4(b*) = |Σ Q_j| / Σ|Q_j|  -> 1 ?
  - quarter IMBALANCE band: r4(b*) = min_j ‖Q_j‖ / max_j ‖Q_j‖  -- bounded away from 0 and 1?
    (stationary across n, like the index-2 band?)
  - the AGGREGATE inflation factor F4 = M / max_j ‖Q_j‖ = Σ‖Q_j‖/max‖Q_j‖ ∈ [1,4]. If F4 is a
    bounded O(1) constant (not →4 = full degeneration-free, not →1 = single-quarter), then the
    index-4 sub-split, like index-2, is a bounded reshuffle with NO √-thinning over the heavier
    quarter AND no single-quarter degeneration.

WHY IT MATTERS (Lever A, dyadic tower coherence): if the coherent-bounded-imbalance picture is
PARTITION-DEPTH-INVARIANT (holds at index-2 AND index-4, presumably any 2^j), then NO dyadic
sub-partition at the worst frequency supplies √-thinning — the tower coherence lever is dead not just
at one level but at every refinement depth. Probe-first; formalize only the conditional band fact.

HARD RULE 1/2: never n=q-1; proper μ_n; p≫n³; multiple structured primes; FULL coset scan to find
the TRUE b*; report median over primes; NO growth-law theorem from a trend.
"""
from __future__ import annotations

import argparse
import math
import numpy as np
import sympy as sp

TAU = 2.0 * math.pi


def primes_1_mod_n(n: int, beta: int, count: int):
    target = n ** beta
    k = max(1, (target - 1 + n - 1) // n)
    out = []
    p = k * n + 1
    while len(out) < count:
        if sp.isprime(p):
            out.append(p)
        p += n
    return out


def worstb_index4(n: int, p: int, chunk: int = 8192):
    """FULL coset scan; at the true argmax b*, return (rho4, r4, F4)."""
    assert n < p - 1 and n % 4 == 0
    m = (p - 1) // n
    g = int(sp.primitive_root(p))
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=object)
    G = np.array([pow(g, m * t, p) for t in range(n)], dtype=object)
    # index-4 quarters by residue class of the exponent t mod 4 (the 4 cosets of μ_{n/4} in μ_n)
    quarters = [G[r::4] for r in range(4)]

    best = -1.0
    best_b = None
    for lo in range(0, m, chunk):
        rr = reps[lo:lo + chunk]
        ph = (rr[:, None] * G[None, :]) % p
        val = np.exp(1j * TAU * ph.astype(np.float64) / p).sum(axis=1)
        a = np.abs(val)
        j = int(np.argmax(a))
        if a[j] > best:
            best = float(a[j])
            best_b = int(rr[j])

    b = best_b
    qsum = []
    for Q in quarters:
        ph = ((b * Q) % p).astype(np.float64)
        qsum.append(np.exp(1j * TAU * ph / p).sum())
    qabs = np.array([abs(z) for z in qsum])
    M = abs(sum(qsum))
    rho4 = M / qabs.sum() if qabs.sum() > 0 else 0.0
    r4 = qabs.min() / qabs.max() if qabs.max() > 0 else 0.0
    F4 = M / qabs.max() if qabs.max() > 0 else 0.0
    return rho4, r4, F4


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--amin", type=int, default=4)
    ap.add_argument("--amax", type=int, default=6)
    ap.add_argument("--beta", type=int, default=4)
    ap.add_argument("--primes", type=int, default=6)
    args = ap.parse_args()

    print(f"# Door-IV worst-b INDEX-4 quarter coherence+band (beta={args.beta}, "
          f"{args.primes} primes/n, FULL coset scan, proper μ_n)\n")
    print(f"{'n':>5} {'rho4 med':>9} {'r4 med':>8} {'r4 min':>8} {'F4 med':>8} {'F4/4':>7}")
    ns, rho4s, r4s, F4s = [], [], [], []
    for a in range(args.amin, args.amax + 1):
        n = 1 << a
        ps = primes_1_mod_n(n, args.beta, args.primes)
        rr, ri, rf = [], [], []
        for p in ps:
            rho4, r4, F4 = worstb_index4(n, p)
            rr.append(rho4); ri.append(r4); rf.append(F4)
        rho4m = float(np.median(rr)); r4m = float(np.median(ri))
        r4min = float(np.min(ri)); F4m = float(np.median(rf))
        ns.append(n); rho4s.append(rho4m); r4s.append(r4m); F4s.append(F4m)
        print(f"{n:>5} {rho4m:>9.4f} {r4m:>8.4f} {r4min:>8.4f} {F4m:>8.4f} {F4m/4:>7.3f}")

    print("\n## VERDICT")
    coh = all(x > 0.99 for x in rho4s)
    band_lo = min(r4s) > 0.05
    band_hi = max(r4s) < 0.999
    F_bounded = all(1.05 < x < 3.95 for x in F4s)
    print(f"quarter coherence rho4≈1 at all n: {coh}  (med rho4 = {[round(x,4) for x in rho4s]})")
    print(f"quarter imbalance r4 in (0,1) band: lo>{0.05}:{band_lo} hi<{0.999}:{band_hi}  "
          f"(med r4 = {[round(x,3) for x in r4s]})")
    print(f"aggregate inflation F4 bounded in (1,4): {F_bounded}  "
          f"(med F4 = {[round(x,3) for x in F4s]})")
    if coh and F_bounded:
        print("PARTITION-DEPTH-INVARIANT: the index-4 split is ALSO coherent (rho4≈1) with a bounded "
              "O(1) inflation F4∈(1,4) over the heaviest quarter — NEITHER single-quarter degeneration "
              "(F4→1) NOR full √-thinning (F4→4). Same coherent-bounded-reshuffle picture as index-2 ⟹ "
              "no dyadic sub-partition at b* thins the wall (Lever A dead at every refinement depth).")
    else:
        print("NOT cleanly partition-depth-invariant; re-examine quarter structure.")
    print("\nPROBE-ONLY (HARD RULE 1/2): no growth-law theorem asserted. CORE remains OPEN.")


if __name__ == "__main__":
    main()
