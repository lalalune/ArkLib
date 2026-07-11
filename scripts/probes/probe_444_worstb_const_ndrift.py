#!/usr/bin/env python3
"""
Door-(iv) Lane-1 probe (#444): n-DRIFT of the worst-b coherence constant at fixed prize-β.

Context. Two prior worst-b findings (DISPROOF_LOG):
  [doorIV-worstb-deficit-fraction-is-n-artifact] : cleanest invariant is the dimensionless
      C(n,β,p) = ρ²(b*) · n / log(p/n) ≈ 1.0–1.6.
  [doorIV-worstb-coherence-constant-prime-stable]: at fixed (n,β), C is PRIME-STABLE with no lower
      tail, and the spread TIGHTENS toward the prize regime.

Both explicitly flagged the OPEN question as the n-ASYMPTOTICS: "the constant could drift slowly with
n (the 25-yr wall lives in the n-asymptotics, not the prime-variation)."  Nobody has measured the SIGN
and RATE of that drift.  That is the single most prize-relevant empirical question on this object:

  - prize TRUE  ⟺  C(n) is bounded as n→∞ (M(n) = O(√(n log(p/n)))).
  - prize FALSE ⟺  C(n) → ∞ (e.g. C(n) ~ n^{2·0.011} from the SOTA n^{0.989} exponent).

This probe fixes β at a prize value and grows n over the largest feasible range (geometric ladder of
2-powers), AVERAGING over a few primes per n (using the established prime-stability), and reports C(n)
plus its successive ratios C(2n)/C(n) and a log-log slope.  A clean flat C(n) is prize-consistent; a
persistent positive slope is the wall.  Empirical only; proves nothing.
"""
from __future__ import annotations

import argparse
import math
import statistics
import numpy as np
import sympy as sp

TAU = 2.0 * math.pi


def primes_1_mod_n(n: int, target: int, count: int):
    out = []
    k = max(1, (target - 1 + n - 1) // n)
    while len(out) < count:
        p = k * n + 1
        if sp.isprime(p):
            out.append(p)
        k += 1
    return out


def worst_rho2(n: int, p: int, chunk: int = 8192) -> float:
    m = (p - 1) // n
    g = int(sp.primitive_root(p))
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)
    G = np.array([pow(g, m * t, p) for t in range(n)], dtype=np.int64)
    best = 0.0
    for lo in range(0, m, chunk):
        rr = reps[lo: lo + chunk]
        ang = (TAU / p) * (np.outer(rr, G) % p)
        s = np.exp(1j * ang).sum(axis=1)
        mag2 = (s.real ** 2 + s.imag ** 2)
        cur = float(mag2.max())
        if cur > best:
            best = cur
    return best / (n * n)


def const_at(n: int, beta: float, num_primes: int):
    target = int(round(n ** beta))
    ps = primes_1_mod_n(n, target, num_primes)
    Cs = []
    for p in ps:
        r2 = worst_rho2(n, p)
        ref = math.log(p / n) / n
        if ref > 0:
            Cs.append(r2 / ref)
    return statistics.mean(Cs), statistics.pstdev(Cs), ps[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--ns", type=int, nargs="+", default=[8, 16, 32, 64, 128])
    ap.add_argument("--num-primes", type=int, default=6)
    ap.add_argument("--max-pminus1", type=int, default=8_000_000,
                    help="skip (n,β) whose p≈n^β exceeds this (keeps the coset scan tractable)")
    args = ap.parse_args()
    print("Door-(iv) worst-b coherence-constant n-DRIFT probe (fixed prize-β)")
    print(f"C(n) = mean over {args.num_primes} primes of ρ²(b*)·n/log(p/n);  β={args.beta}")
    print("prize TRUE ⟺ C(n) bounded; prize FALSE ⟺ C(n)→∞.\n")
    print(f"{'n':>6} {'p0':>12} {'C(n)':>9} {'std':>7} {'C(2n)/C(n)':>11} {'loglog slope':>13}")
    rows = []
    prevC = None
    prevlogn = None
    for n in args.ns:
        if n ** args.beta > args.max_pminus1:
            print(f"{n:>6}  (skipped: n^β≈{int(n**args.beta)} > {args.max_pminus1})")
            continue
        C, std, p0 = const_at(n, args.beta, args.num_primes)
        ratio = (C / prevC) if prevC else float("nan")
        slope = ((math.log(C) - math.log(prevC)) / (math.log(n) - prevlogn)) if prevC else float("nan")
        print(f"{n:>6} {p0:>12} {C:>9.4f} {std:>7.4f} {ratio:>11.4f} {slope:>13.4f}")
        rows.append((n, C, ratio, slope))
        prevC, prevlogn = C, math.log(n)
    if len(rows) >= 2:
        # overall log-log least-squares slope of C(n) vs n
        xs = [math.log(n) for (n, _, _, _) in rows]
        ys = [math.log(C) for (_, C, _, _) in rows]
        mx, my = statistics.mean(xs), statistics.mean(ys)
        num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        den = sum((x - mx) ** 2 for x in xs)
        overall = num / den if den else float("nan")
        print(f"\nOVERALL log-log slope of C(n) vs n (β={args.beta}): {overall:+.4f}")
        print("  slope ≈ 0  → C(n) flat (prize-consistent, bounded constant).")
        print("  slope > 0 persistently → C(n) grows (the wall: M(n) super-√).")
        print("  (reference: SOTA exponent n^0.989 ⟹ C(n)~n^0.022, slope ≈ +0.022.)")


if __name__ == "__main__":
    main()
