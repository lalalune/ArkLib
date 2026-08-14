#!/usr/bin/env python3
"""
A10 entropy-compression -- THE DECISIVE p-SCALING TEST (algebraic vs modular collisions).

Probe 1 found a REAL gain: H(subset-sum dist over mu_n) < log2 C(n,t), smooth < random.
The PRIZE needs this gain to SURVIVE p -> infinity (prize regime p >> n^3) AND be large
enough to push the list below budget PAST Johnson.

CRITICAL DISTINCTION the manifesto demands I resolve:
 - MODULAR collisions: subset sums coincide only after reducing mod p (small-p wraparound).
   These VANISH as p grows -> H -> log2 C(n,t) = max entropy = VOLUME = the wall.
 - ALGEBRAIC collisions: subset sums coincide as ELEMENTS of Z[zeta_n] (exact, p-independent).
   For mu_n = {zeta^0,...,zeta^{n-1}} embedded via a generator h mod p, a collision
   "sum over T = sum over T'" mod p for ALL large p <=> the corresponding sum of roots of
   unity is equal in Z[zeta_n] <=> a VANISHING-SUM / Mann relation. These persist.

Method: sweep p (proper, p>>n^3, increasing). The #distinct subset sums mod p INCREASES
toward a CEILING = #distinct sums in Z[zeta_n] (algebraic). If the ceiling = C(n,t) (all
distinct algebraically) then gain -> 0 (wall). If ceiling < C(n,t), the residual gain is
algebraic (Mann/vanishing-sum structure) -- but is it constant-factor or exponent-level?

For large C(n,t) we MONTE-CARLO the entropy (collision-probability / sample), exact for small.

PROPER REGIME: p PRIME, n=2^mu, n|p-1, p>>n^3. NEVER n=p-1.
"""
import itertools, math, sys, random
from collections import Counter
from math import comb, log2, lgamma

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % m == 0: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def primes_1modn_above(n, lo, count):
    out = []; t = ((lo // n) + 1) * n + 1
    while len(out) < count:
        if isprime(t): out.append(t)
        t += n
    return out

def subgroup(p, n):
    fac = []; x = p-1; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for c in range(2, p):
        if all(pow(c, (p-1)//q, p) != 1 for q in fac):
            g = c; break
    h = pow(g, (p-1)//n, p)
    H = [pow(h, i, p) for i in range(n)]
    assert len(set(H)) == n and pow(h, n//2, p) != 1
    return H

def log2binom(n, k):
    if k < 0 or k > n: return float("-inf")
    if k in (0, n): return 0.0
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/math.log(2)

def exact_H_and_distinct(D, t, p):
    cnt = Counter()
    for cmb in itertools.combinations(D, t):
        cnt[sum(cmb) % p] += 1
    total = comb(n_global, t)
    H = -sum((c/total)*log2(c/total) for c in cnt.values() if c)
    return H, len(cnt)

def mc_H_and_distinct(D, t, p, nsamp=400000):
    """Monte-Carlo: estimate entropy via sampled collision count is biased; instead
    estimate #distinct via sample coverage and H via plug-in on sampled histogram
    (lower bound on H). We report a *collision-rate* estimate of effective support."""
    n = len(D)
    seen = Counter()
    for _ in range(nsamp):
        T = random.sample(D, t)
        seen[sum(T) % p] += 1
    # plug-in entropy of the SAMPLED distribution (this estimates H if support<<nsamp,
    # else lower-bounds the support count). Also report collision rate.
    tot = nsamp
    Hsamp = -sum((c/tot)*log2(c/tot) for c in seen.values() if c)
    # birthday/collision estimate of true support N: P(collision)=~ sum p_i^2.
    # We instead just report #distinct seen (a lower bound on true support) and Hsamp.
    return Hsamp, len(seen)

def main():
    global n_global
    print("A10 p-SCALING (algebraic vs modular collisions):")
    print("track #distinct subset-sums mod p as p grows. Ceiling = algebraic distinct count.")
    print("gain = log2 C(n,t) - H. H-collapse: ceiling=C, gain->0 (=volume=wall).")
    print()
    random.seed(11)
    for (mu, t) in [(4, 4), (4, 8), (5, 8)]:
        n = 1 << mu; n_global = n
        if t > n: continue
        l2c = log2binom(n, t)
        Cval = comb(n, t)
        print(f"--- n={n}, t={t}, log2 C(n,t)={l2c:.4f}, volume C={Cval} ---")
        ps = []
        for e in (3.2, 4.0, 5.0, 6.0):
            ps += primes_1modn_above(n, int(n**e), 1)
        print(f"{'p':>16} {'p/n^3':>11} {'method':>6} {'#distinct':>10} {'dist/C':>7} {'H bits':>9} {'gain':>8}")
        for p in ps:
            D = subgroup(p, n)
            if Cval <= 300000:
                H, nd = exact_H_and_distinct(D, t, p); meth="exact"
            else:
                H, nd = mc_H_and_distinct(D, t, p); meth="MC"
            gain = l2c - H
            print(f"{p:>16} {p/n**3:>11.1f} {meth:>6} {nd:>10} {nd/Cval:>7.4f} {H:>9.4f} {gain:>8.4f}")
        print()

    print("VERDICT: if #distinct -> C(n,t) (dist/C -> 1) as p grows, collisions are MODULAR")
    print("artifacts => gain->0 => A10 = volume = the wall. If dist/C plateaus < 1, residual is")
    print("ALGEBRAIC (Mann). Then ask: is the algebraic deficit exponent-level (cracks) or O(1)?")
    return 0

if __name__ == "__main__":
    sys.exit(main())
