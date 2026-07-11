#!/usr/bin/env python3
"""
#407 / Strategy 1 + 3 — independent verification of the central reduction AND a fresh
attempt to bound the char-p anomaly Anom_r(p) WITHOUT the per-r Wick hierarchy.

SETUP (all exact, no sampling unless stated):
  n = 2^mu, p prime, p = 1 mod n, mu_n = <g> the n-th roots in F_p.
  eta_b = sum_{x in mu_n} e_p(b x),  M(n) = max_{b != 0} |eta_b|.
  E_r(F_p) = #{(x,y) in mu_n^{2r}: sum x = sum y mod p} = (1/p) sum_b |eta_b|^{2r}  (coll count)
  A_r := (1/p) sum_{b != 0} |eta_b|^{2r} = E_r(F_p) - n^{2r}/p              (DC-subtracted moment)
  R_r := ring count = #{(x,y): sum x = sum y in Z[zeta_n]}                  (char-0 collisions)
  Anom_r := E_r(F_p) - R_r >= 0                                            (char-p-only collisions)
  Wick   := (2r-1)!! n^r.

THE PRIZE ENERGY LEMMA:  A_r <= Wick  for all r <= ~log p.
  <=>  Anom_r <= n^{2r}/p + (Wick - R_r).  Since R_r <= Wick (PROVEN, Lam-Leung), the
       SUFFICIENT clean form is  Anom_r <= n^{2r}/p  (directive's stated open inequality).

NEW QUESTIONS THIS PROBE ANSWERS:
 (Q1) Verify A_r <= Wick, decreasing, to deep r, independently (no FFT roundoff: exact int conv).
 (Q2) Measure the EXACT margin Wick - A_r and Wick - R_r: is the char-0 slack already enough
      that Anom_r <= n^{2r}/p is NOT needed (i.e. is R_r << Wick, absorbing the anomaly)?
 (Q3) Structural: is Anom_r itself = sum over SHORT char-p vanishing relations, and does its
      growth match a SINGLE geometric law (Anom_r ~ C(n)^r * something)?  A clean law would
      let a generating-function (Bernstein) bound replace the per-r Wick hierarchy.
 (Q4) The KEY new test: does  sum_r Anom_r t^r  have radius of convergence forced by the
      SHORTEST char-p relation length L_min, and is the per-r contribution <= n^{2r}/p in the
      prize regime BECAUSE L_min > 2 log p there?  (i.e. is the anomaly's onset r controlled?)
"""
import math
from sympy import primerange, isprime
import numpy as np
from collections import defaultdict


def find_gen(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and (n == 1 or pow(g, n // 2, p) == p - 1):
            return g
    raise RuntimeError("no gen")


def fp_coll_exact(n, r, p):
    """Exact E_r(F_p) via integer convolution of the indicator of mu_n on Z/p, r-fold."""
    g = find_gen(n, p)
    mu = [pow(g, j, p) for j in range(n)]
    cnt = np.zeros(p, dtype=object)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=object)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return int(sum(int(c) * int(c) for c in cnt))


def ring_count(n, r):
    """Char-0 collision count R_r via coord vectors in Z[zeta_n] integral basis (zeta^{n/2}=-1)."""
    h = n // 2
    V = []
    for j in range(n):
        v = [0] * h
        if j < h:
            v[j] = 1
        else:
            v[j - h] = -1
        V.append(tuple(v))
    dist = defaultdict(int)
    dist[tuple([0] * h)] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for v in V:
                key = tuple(a + b for a, b in zip(s, v))
                nd[key] += c
        dist = nd
    return sum(c * c for c in dist.values())


def doublefact(r):
    d = 1.0
    for j in range(1, 2 * r, 2):
        d *= j
    return d


def main():
    print("=" * 100)
    print("Q1/Q2 — A_r vs Wick and the char-0 slack R_r vs Wick (prize regime beta=4), EXACT")
    print("=" * 100)
    print(f"{'n':>5} {'p':>10} {'r':>3} {'A_r/Wick':>10} {'R_r/Wick':>10} {'Anom_r':>14} "
          f"{'n^2r/p':>14} {'Anom<=n2r/p?':>13} {'Wick-A_r>=0?':>12}")
    for mu in [3, 4, 5]:
        n = 2 ** mu
        p = next(q for q in primerange(int(n ** 4), int(n ** 4 * 3)) if q % n == 1)
        rmax = 6 if n <= 16 else 5
        for r in range(1, rmax + 1):
            Efp = fp_coll_exact(n, r, p)
            Rr = ring_count(n, r)
            Ar = Efp - n ** (2 * r) / p
            W = doublefact(r) * n ** r
            anom = Efp - Rr
            dc = n ** (2 * r) / p
            print(f"{n:>5} {p:>10} {r:>3} {Ar / W:>10.4f} {Rr / W:>10.4f} {anom:>14d} "
                  f"{dc:>14.2f} {str(anom <= dc):>13} {str(Ar <= W):>12}")
        print()


if __name__ == "__main__":
    main()
