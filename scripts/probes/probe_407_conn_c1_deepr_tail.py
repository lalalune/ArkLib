#!/usr/bin/env python3
"""
#407 C1 (deep-r tail) — how far do the GENUINE count-bad primes extend for r=3,4 (the deep regime)?

The saturation-vs-r probe showed genuine bad primes (p > p_sat=|H^(+r)|) extend past s^3 for
r>=3.  Decisive remaining question: do they TERMINATE at some moderate threshold T(s,r), or do
they continue toward exp(s)?  If T(s,r) is moderate (e.g. < s^4) the count is still clean at the
prize prize q ~ n*2^128 (massive).  If T(s,r) ~ exp(s), the single-r count re-hits BGK.

We scan p == 1 mod s up to a LARGE ceiling and report the LAST genuine bad prime found, plus a
density curve (fraction of primes in each decade that are bad).  Exact convolution; O(p*s*r) per
prime, feasible to p ~ 10^6 for s<=16.
"""
import sys
from collections import Counter
from sympy import isprime, primitive_root


def fp_root(s, p):
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // s, p)


def count_Fp(s, r, p, g=None):
    if g is None:
        g = fp_root(s, p)
    roots = [pow(g, i, p) for i in range(s)]
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for c, m in dist.items():
            for v in roots:
                nd[(c + v) % p] += m
        dist = nd
    return len(dist)


def count_char0(s, r):
    h = s // 2
    rootvecs = [((i % h), (-1 if ((i // h) % 2) == 1 else 1)) for i in range(s)]
    dist = Counter({tuple([0] * h): 1})
    for _ in range(r):
        nd = Counter()
        for vkey, m in dist.items():
            for (col, sgn) in rootvecs:
                lst = list(vkey)
                lst[col] += sgn
                nd[tuple(lst)] += m
        dist = nd
    return len(dist)


def main():
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    PMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 200000

    N0c0 = count_char0(s, r)
    psat = N0c0
    print(f"s={s} r={r}  |H^(+r)|=N0_char0={N0c0}  p_sat={psat}  scan p<= {PMAX}")
    print(f"  thresholds: s^2={s*s} s^3={s**3} s^4={s**4}  2^s={2**s:.3e}")

    last_genuine = 0
    n_bad = 0
    n_scanned = 0
    # decade buckets for density
    import math
    buckets = {}  # decade -> [bad, total]
    p = 1
    p = p - (p % s) + 1
    if p <= 1:
        p += s
    while p <= PMAX:
        if p > 2 and isprime(p):
            n_scanned += 1
            c = count_Fp(s, r, p)
            isbad = (c != N0c0)
            dec = int(math.log10(p))
            b = buckets.setdefault(dec, [0, 0])
            b[1] += 1
            if isbad:
                b[0] += 1
                n_bad += 1
                if p > psat:
                    last_genuine = p
        p += s

    print(f"  scanned {n_scanned} primes == 1 mod {s};  total bad={n_bad}")
    print(f"  LAST GENUINE bad prime (p > p_sat): {last_genuine}"
          + ("  <-- none genuine" if last_genuine == 0 else ""))
    if last_genuine:
        print(f"     last_genuine/s^2={last_genuine/s/s:.2f}  /s^3={last_genuine/s**3:.3f}  "
              f"/s^4={last_genuine/s**4:.4f}  log2={math.log2(last_genuine):.2f}  vs s={s}")
    print("  density by decade (badcount/total):")
    for dec in sorted(buckets):
        b = buckets[dec]
        print(f"    10^{dec}: {b[0]}/{b[1]} = {b[0]/b[1]:.3f}")


if __name__ == "__main__":
    main()
