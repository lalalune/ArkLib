#!/usr/bin/env python3
"""
Door-(iv) Lane-1 probe (#444): PRIME-STABILITY of the worst-b coherence constant.

Context. The latest worst-b deficit-fraction probe (sol, DISPROOF_LOG entry
[doorIV-worstb-deficit-fraction-is-n-artifact]) found the cleanest measured invariant is

    C(n, beta, p) := rho^2(b*) * n / log(p/n)   ~ 1.0 .. 1.6

across (n in {16,32}, beta in {3..6}).  That probe varied ONE prime per (n,beta).

NEW QUESTION (not previously measured): at FIXED (n, beta), how STABLE is C across the
MANY primes p ≡ 1 (mod n) with p ~ n^beta?  The prize is ∀-field-universal (#444 c.154:
no "good prime exists" pigeonhole escape).  Empirically, that predicts C should NOT have a
heavy lower tail at fixed (n,beta) -- i.e. there is no prime that makes rho^2(b*) anomalously
small (which a good-prime lever would need).  We measure the SPREAD of C over a window of
primes and report min/median/max + coefficient of variation.

This is a worst-b SCAN over all m=(p-1)/n quotient cosets, exact (no moment / completion /
energy route).  Empirical only.  It validates (or would refute) prime-stability of the
prize-reference constant; it proves nothing.
"""
from __future__ import annotations

import argparse
import math
import statistics
import numpy as np
import sympy as sp

TAU = 2.0 * math.pi


def primes_1_mod_n(n: int, target: int, count: int):
    """The `count` smallest primes p ≡ 1 (mod n) with p >= target."""
    out = []
    k = max(1, (target - 1 + n - 1) // n)
    while len(out) < count:
        p = k * n + 1
        if sp.isprime(p):
            out.append(p)
        k += 1
    return out


def worst_rho2(n: int, p: int, chunk: int = 4096) -> float:
    """rho^2(b*) = max_b |eta_b|^2 / n^2 over the (p-1)/n quotient cosets."""
    m = (p - 1) // n
    g = int(sp.primitive_root(p))
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)
    G = np.array([pow(g, m * t, p) for t in range(n)], dtype=np.int64)
    best = 0.0
    for lo in range(0, m, chunk):
        rr = reps[lo: lo + chunk]
        # phases: (b * G) / p, b over rr, summed over the subgroup G
        ang = (TAU / p) * (np.outer(rr, G) % p)
        s = np.exp(1j * ang).sum(axis=1)
        mag2 = (s.real ** 2 + s.imag ** 2)
        cur = float(mag2.max())
        if cur > best:
            best = cur
    return best / (n * n)


def run(n: int, beta: int, num_primes: int):
    target = n ** beta
    ps = primes_1_mod_n(n, target, num_primes)
    rows = []
    for p in ps:
        r2 = worst_rho2(n, p)
        ref = math.log(p / n) / n          # prize reference  log(p/n)/n
        C = r2 / ref if ref > 0 else float("nan")
        rows.append((p, r2, C))
    Cs = [c for (_, _, c) in rows]
    cmin, cmed, cmax = min(Cs), statistics.median(Cs), max(Cs)
    cmean = statistics.mean(Cs)
    cstd = statistics.pstdev(Cs)
    cv = cstd / cmean if cmean else float("nan")
    print(f"\n=== n={n}  beta={beta}  ({num_primes} primes p≡1 mod n, p≥n^beta={target}) ===")
    print(f"{'p':>12} {'rho2(b*)':>10} {'C=rho2*n/log(p/n)':>20}")
    for (p, r2, C) in rows:
        print(f"{p:>12} {r2:>10.4f} {C:>20.4f}")
    print(f"  C: min={cmin:.4f}  median={cmed:.4f}  max={cmax:.4f}  mean={cmean:.4f}  "
          f"std={cstd:.4f}  CV={cv:.4f}  spread(max/min)={cmax/cmin:.3f}")
    return cmin, cmed, cmax, cv, cmax / cmin


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", type=int, nargs="+", default=[16, 32])
    ap.add_argument("--betas", type=int, nargs="+", default=[3, 4, 5])
    ap.add_argument("--num-primes", type=int, default=12)
    args = ap.parse_args()
    print("Door-(iv) worst-b coherence-constant PRIME-STABILITY probe")
    print("C(n,beta,p) = rho^2(b*) * n / log(p/n);  ∀-field-universality predicts low spread,")
    print("in particular NO heavy lower tail (no prime making rho^2(b*) anomalously small).")
    summary = []
    for n in args.ns:
        for beta in args.betas:
            if n ** beta > 6_000_000:    # keep the per-prime scan tractable
                continue
            cmin, cmed, cmax, cv, spread = run(n, beta, args.num_primes)
            summary.append((n, beta, cmin, cmed, cmax, cv, spread))
    print("\n=== SUMMARY (spread of the prize-reference constant over primes) ===")
    print(f"{'n':>4} {'beta':>5} {'Cmin':>8} {'Cmed':>8} {'Cmax':>8} {'CV':>7} {'max/min':>8}")
    for (n, beta, cmin, cmed, cmax, cv, spread) in summary:
        print(f"{n:>4} {beta:>5} {cmin:>8.3f} {cmed:>8.3f} {cmax:>8.3f} {cv:>7.3f} {spread:>8.3f}")


if __name__ == "__main__":
    main()
