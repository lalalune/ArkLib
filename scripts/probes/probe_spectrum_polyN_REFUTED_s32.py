#!/usr/bin/env python3
"""
probe_spectrum_polyN_REFUTED_s32.py  (#444)  — REFUTATION of the F1 "poly(n)=n" open-core claim.

The F1 floor claimed the single open prize core is
    CompleteHomogeneousSpectrumBound:  #{distinct h_r(R): R in binom(mu_s,k+1)} <= n * C(s+r-1, r),
i.e. with poly(n) = n, "verified in all measured cases (s=8,16, r<=6)".

THIS REFUTES THAT GENERAL FORM. poly(n)=n was only ever tested at s=8,16. Extending to the next
power of two s=32 (prize regime is s=2^mu), the bound FAILS at small r:
  - exact (full enumeration) s=24,28: r=2 needs poly=389, 3444 (>> n; GROWING ~16n, 123n);
  - SAMPLE (only lower-bounds the true count) s=32, k+1=9:
        r=2: ceil = 32*C(33,2) = 16896, but >16896 DISTINCT VALUES already appear in a sample -> FALSE
        r=3: ceil = 32*C(34,3) = 191488, but >191488 appear in a sample          -> FALSE

So the spectrum's distinct-value count at SMALL r grows FASTER than n*C(s+r-1,r): at fixed rho the
witness size k+1 = rho*s grows, so the trivial ceiling C(s,k+1) is EXPONENTIAL, and at small r there
is too little symmetric-function collision to bring it under the polynomial n*C(s+r-1,r). The bound
DOES hold at large r (s=24: r>=4 OK; s=28: r>=4 OK) -- so it is a SMALL-r phenomenon. Whether the
delta*-binding fold r=M_cross lies in the holds-regime (large r) or the fails-regime (small r) is the
real open question; the "clean poly(n)=n combinatorial core" framing is REFUTED.

This script reproduces the s=32 sample refutation deterministically.
"""
import random
from math import comb

def isprime(x):
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return x > 1

def gen_prime(s, lo):
    p = max(lo, s + 1)
    while not (p % s == 1 and isprime(p)):
        p += 1
    return p

def subgroup(s, p):
    for g in range(2, p):
        h = pow(g, (p - 1) // s, p)
        if pow(h, s, p) == 1 and all(pow(h, s // q, p) != 1 for q in [2] if s % q == 0):
            return [pow(h, i, p) for i in range(s)]

def hsym(R, r, p):
    dp = [0] * (r + 1)
    dp[0] = 1
    for x in R:
        ndp = dp[:]
        for j in range(1, r + 1):
            ndp[j] = (dp[j] + x * ndp[j - 1]) % p
        dp = ndp
    return dp[r]

def main():
    random.seed(12345)
    N = 2_000_000
    any_refuted = False
    for s in (16, 32):
        p = gen_prime(s, 50 * s ** 4)
        S = subgroup(s, p)
        k = s // 4                      # k+1 = s/4 + 1  (prize rho = 1/4)
        for r in (2, 3):
            ceil_val = s * comb(s + r - 1, r)
            seen = set()
            for _ in range(N):
                R = random.sample(S, k + 1)
                seen.add(hsym(R, r, p))
                if len(seen) > ceil_val:
                    break
            refuted = len(seen) > ceil_val
            any_refuted = any_refuted or refuted
            tag = "REFUTED (sample exceeds ceiling)" if refuted else "sample-consistent"
            print(f"s={s:>2} k+1={k+1} r={r}: ceil=n*C(s+r-1,r)={ceil_val:>7}  "
                  f"#distinct_seen>={len(seen):>7}  -> {tag}")
    print()
    print("VERDICT:", "poly(n)=n spectrum bound is REFUTED at s=32 (prize power-of-2)."
          if any_refuted else "no refutation found (unexpected)")

if __name__ == "__main__":
    main()
