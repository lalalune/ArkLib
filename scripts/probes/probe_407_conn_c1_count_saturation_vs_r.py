#!/usr/bin/env python3
"""
#407 CONNECTION C1 (decisive) — does the bad-scalar COUNT saturate at SMALL p for the
WORST-CASE r, or does its saturation threshold ITSELF grow with r (re-hitting BGK)?

The previous probe showed: for r=2 the count N0(F_p)=N0_char0 above a small prime (max bad ~
s^2/s^3), BUT for r=3 the count was STILL not saturated at p=577 for s=16.  This probe pins
down the count's saturation threshold p*(s,r) := max bad prime for N0 (the largest p with
N0(F_p) != N0_char0), as a function of r, to decide:

  HYPOTHESIS H1 (count bypasses BGK):  p*(s,r) is SMALL (<= poly(s)) for ALL r up to log s.
  HYPOTHESIS H2 (count re-hits BGK):   p*(s,r) GROWS with r, reaching exp(s) at r ~ log s.

Decisive because delta* is realized at the WORST-CASE r (KB: r = rho*s + 2, with the prize
worst case at a SMALL subgroup s ~ log n, r ~ rho*s+2).  If the count's saturation threshold at
THAT r is small, the count is clean at the prize prime -> genuine bypass.  If it grows with r,
the single-r count is itself a deep object.

We also separately report, for char-0, |H^(+r)|(mu_s) (the saturation TARGET) and the SATURATION
prime  p_sat := |H^(+r)| (above which the sumset cannot even FIT char-0-many values -- the
trivial information-theoretic floor).  A count bad prime BELOW p_sat is a genuine collision;
ABOVE p_sat the count is forced < N0_char0 by pigeonhole (the sumset is the whole field-ish).

This separates: 'count not saturated because p < |H^(+r)|' (trivial, the SATURATION artifact the
KB flagged) from 'count not saturated despite p >> |H^(+r)|' (a genuine deep-collision = BGK).
"""
import sys
from collections import Counter
from sympy import isprime, primitive_root


def primes_1modn(n, count, lo=None):
    out = []
    p = lo or 1
    p = p - (p % n) + 1
    if p <= (lo or 1):
        p += n
    while len(out) < count:
        if p > 2 and isprime(p):
            out.append(p)
        p += n
    return out


def fp_root(s, p):
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // s, p)


def count_Fp(s, r, p):
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
    rootvecs = []
    for i in range(s):
        col = i % h
        sgn = -1 if ((i // h) % 2) == 1 else 1
        rootvecs.append((col, sgn))
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
    PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
    print("=" * 100)
    print(f"C1 — count saturation threshold p*(s,r) vs r  (scan p<= {PMAX})")
    print("decisive: does p* (largest bad prime for the COUNT) stay SMALL, or grow with r?")
    print("p_sat = |H^(+r)| is the information-theoretic floor (below it, the count CANNOT saturate)")
    print("=" * 100)

    for s in [8, 16]:
        rmax = {8: 4, 16: 4}[s]
        print(f"\n  s={s}  (h=s/2={s//2}; worst-case r ~ rho*s+2 in [3, {rmax}] for small rho)")
        print(f"    {'r':>2} {'|H^(+r)|':>9} {'p_sat~':>7} | {'p*=maxbad':>10} {'#bad':>5} {'p*/s^2':>7} {'p*<p_sat?':>9} {'p*<s^3?':>8}")
        for r in range(2, rmax + 1):
            N0c0 = count_char0(s, r)
            psat = N0c0  # the sumset cannot have more than this many values; bad primes below it
            # scan all primes == 1 mod s up to PMAX, find bad ones
            badprimes = []
            allp = primes_1modn(s, 100000, lo=2)
            scanned = 0
            for p in allp:
                if p > PMAX:
                    break
                scanned += 1
                if count_Fp(s, r, p) != N0c0:
                    badprimes.append(p)
            pstar = max(badprimes) if badprimes else 0
            # genuine = bad primes that are ABOVE p_sat (not a fit artifact)
            genuine = [p for p in badprimes if p > psat]
            pstar_genuine = max(genuine) if genuine else 0
            print(f"    {r:>2} {N0c0:>9} {psat:>7} | {pstar:>10} {len(badprimes):>5} "
                  f"{pstar/(s*s):>7.2f} {str(pstar<psat):>9} {str(pstar<s**3):>8}")
            if genuine:
                print(f"         GENUINE bad primes (p > p_sat={psat}, NOT a fit artifact): "
                      f"{genuine[:8]}{'...' if len(genuine)>8 else ''}  max={pstar_genuine}")
            else:
                print(f"         all {len(badprimes)} bad primes are <= p_sat={psat} "
                      f"(FIT ARTIFACTS) -> NO genuine bad prime; count saturates exactly at p_sat")


if __name__ == "__main__":
    main()
