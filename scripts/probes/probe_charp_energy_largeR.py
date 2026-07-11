#!/usr/bin/env python3
"""
probe_charp_energy_largeR.py

Decisive on-regime test of the prize energy bound  E_r(F_p) <= (2r-1)!!*n^r
for the THIN regime (p in [n^4, n^5]), pushing to PRIZE-SCALE moment r ~ ln q.

Two parts:
  A) WORST-CASE SWEEP at fixed moderate r over EVERY prime p = 1 mod n in the thin
     window: is there ANY thin prime that violates the Gaussian bound? (int64 exact)
  B) LARGE-r EXTENSION at sampled primes (incl. known special/Fermat primes) up to
     r=40: does the sub-Gaussian (ratio<1, decreasing) trend survive toward r~ln q,
     or does the excess W_r eventually break the bound? (float64; ratio needs only
     ~3 digits, exact-integer would overflow int64 for large r.)

The sup-norm consequence: max_a|S(a)| <= (p*E_r)^{1/2r}; with E_r<=(2r-1)!!*n^r and
p~n^4 this gives ~ sqrt(8 ln n)*sqrt(n) cancellation at r~ln p — the BGK target.
So "bound holds to r~ln p, worst-case over thin p"  <=>  the prize sup-norm bound.
"""
import numpy as np
from sympy import isprime, primitive_root

def dfact(m):
    p, k = 1, m
    while k > 0:
        p *= k; k -= 2
    return p

def subgroup(p, n):
    g = pow(primitive_root(p), (p - 1) // n, p)
    R, cur = [], 1
    for _ in range(n):
        R.append(cur); cur = (cur * g) % p
    return R

def energy_int(p, R, r):
    """exact int64 E_r (use only when E_r < 2^63)."""
    c = np.zeros(p, dtype=np.int64)
    for x in R: c[x] += 1
    for _ in range(r - 1):
        new = np.zeros(p, dtype=np.int64)
        for x in R: new += np.roll(c, x)
        c = new
    cc = c.astype(object); return int(np.sum(cc * cc))

def energy_float_ratio(p, R, r, Gr):
    """E_r/Gr via float64 (for large r where int64 overflows)."""
    c = np.zeros(p, dtype=np.float64)
    for x in R: c[x] += 1.0
    for _ in range(r - 1):
        new = np.zeros(p, dtype=np.float64)
        for x in R: new += np.roll(c, x)
        c = new
    return float(np.sum(c * c) / Gr)

def thin_primes_all(n, hi_mult, cap=None):
    lo, hi = n**4, min(n**5, n**4 * hi_mult)
    out = []
    cand = lo - (lo % n) + 1
    if cand < lo: cand += n
    while cand <= hi:
        if isprime(cand): out.append(cand)
        cand += n
        if cap and len(out) >= cap: break
    return out, lo, hi

def main():
    # ---- PART B first (most important): does sub-Gaussian survive to prize r? ----
    print("=== PART B: large-r extension toward prize r~ln q (sampled thin primes) ===\n")
    for n, hi_mult in [(8, 8), (16, 12)]:
        allp, lo, hi = thin_primes_all(n, hi_mult)
        idx = sorted(set([0, len(allp)//4, len(allp)//2, 3*len(allp)//4, len(allp)-1]))
        sample = [allp[i] for i in idx]
        if isprime(n**4 + 1) and (n**4 + 1) not in sample:   # Fermat prime n=16 -> 65537
            sample = sorted(set(sample + [n**4 + 1]))
        rs = [2, 4, 6, 8, 12, 16, 20, 28, 40]
        print(f"  --- n={n}, sampled primes {sample} ---")
        print("    r:  " + "  ".join(f"{r:>6}" for r in rs))
        for p in sample:
            R = subgroup(p, n)
            row = [energy_float_ratio(p, R, r, dfact(2*r-1) * n**r) for r in rs]
            mark = "  <--EXCEEDS@some r" if any(x > 1.0 for x in row) else ""
            print(f"  p={p:>8}: " + "  ".join(f"{x:6.3f}" for x in row) + mark)
        print()

    # ---- PART A: worst-case sweep at fixed r (n=8 exhaustive, n=16 sampled) ----
    print("=== PART A: worst-case sweep, fixed r, thin primes p=1 mod n ===\n")
    for n, rfix, hi_mult, cap in [(8, 6, 8, None), (16, 6, 16, 400)]:
        primes, lo, hi = thin_primes_all(n, hi_mult, cap=cap)
        Gr = dfact(2 * rfix - 1) * n**rfix
        best, bp, viol = -1.0, None, []
        for p in primes:
            ratio = energy_int(p, subgroup(p, n), rfix) / Gr
            if ratio > best: best, bp = ratio, p
            if ratio > 1.0: viol.append((p, round(ratio, 4)))
        tag = "EXHAUSTIVE" if cap is None else f"first {cap} sampled"
        print(f"  n={n} r={rfix}: {len(primes)} thin primes in [{lo},{hi}] ({tag})  "
              f"sup E_r/G_r = {best:.4f} (p={bp})  violations(>1): {len(viol)}")
        if viol: print(f"     VIOLATORS: {viol[:8]}")
    print()

if __name__ == "__main__":
    main()
