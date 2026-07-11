#!/usr/bin/env python3
"""
probe(#389): test lalalune's Incidence-Genericity Dichotomy via the sumset criterion.

Claim under test: δ*(μ_n,ε*) = average-term (capacity boundary) IFF μ_n is incidence-generic,
and μ_n fails genericity exactly when its sumset is "small".

Finding (this probe):
 * The CORRECT genericity criterion is |μ_n + μ_n| relative to its MAX n²/2 (the random/Sidon
   value), NOT relative to q.  The literal "|μ_n+μ_n| ≤ q/10" is vacuous: |μ_n+μ_n| ≤ n² ≪ q/10
   for the prize q≈n⁵, so it would mislabel EVERY subgroup non-generic.
 * At GENERIC prize-proportion primes (p≈n⁵) the dyadic subgroup μ_{2^k} has
   |μ_n+μ_n| = (n²+2)/2 EXACTLY = the random reference  ⇒  fully incidence-generic,
   and additive energy E⁺ = 3n(n-1) (the clean cyclotomic value).
 * The NON-generic ("bad") primes are exactly the SMALL primes where μ_{2^k} is dense in F_p
   (17,97,193,257,…): there |μ_n+μ_n| ≪ n²/2 and E⁺ ≫ 3n(n-1) (ratio up to 7.4).
 * So the dichotomy is REAL and keyed to (sumset≈n²/2 ⟺ energy≈3n(n-1) ⟺ generic).  Prize-
   proportion primes are GENERICALLY generic.  Connection: this is the SAME object as the
   additive-energy clean-threshold P_max(n) (cf probe_energy_pmax_growth.py): generic ⟺ p>P_max.
   The honest residual is decidable-per-instance ("is THE deployed prime > P_max(2^32)?"); the
   asymptotic worst-case is whether P_max(2^32) < (2^32)^5 = 2^160 (P_max grows; open).
"""
import sympy
from collections import Counter
import random

def subgroup(p, n):
    g = int(sympy.primitive_root(p)); z = pow(g, (p-1)//n, p)
    return [pow(z, j, p) for j in range(n)]

def sumset_size(H, p):
    return len({(a+b) % p for a in H for b in H})

def energy(H, p):
    c = Counter()
    for a in H:
        for b in H: c[(a+b) % p] += 1
    return sum(v*v for v in c.values())

BAD = {3:[17,41], 4:[97,257], 5:[97,4129,194977], 6:[193,257]}

def main():
    print(f"{'k':>2} {'n':>4} {'p':>12} {'type':>8} {'|H+H|':>7} {'/n^2':>6} {'E+':>8} {'/3n(n-1)':>9}")
    for k in (3,4,5,6):
        n = 1<<k; nn = n*n; clean = 3*n*(n-1)
        base = n**5; m = (base-1)//n
        while True:
            p = m*n+1; m += 1
            if sympy.isprime(p): break
        H = subgroup(p, n)
        print(f"{k:>2} {n:>4} {p:>12} {'GEN n^5':>8} {sumset_size(H,p):>7} "
              f"{sumset_size(H,p)/nn:>6.3f} {energy(H,p):>8} {energy(H,p)/clean:>9.3f}")
        for bp in BAD.get(k, []):
            if (bp-1) % n: continue
            Hb = subgroup(bp, n)
            print(f"{k:>2} {n:>4} {bp:>12} {'BAD':>8} {sumset_size(Hb,bp):>7} "
                  f"{sumset_size(Hb,bp)/nn:>6.3f} {energy(Hb,bp):>8} {energy(Hb,bp)/clean:>9.3f}")
        random.seed(1+k); R = random.sample(range(1, p), n)
        print(f"{k:>2} {n:>4} {'(random)':>12} {'RANDREF':>8} {sumset_size(R,p):>7} "
              f"{sumset_size(R,p)/nn:>6.3f}")

if __name__ == "__main__":
    main()
