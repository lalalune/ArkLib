#!/usr/bin/env python3
"""
PROBE 2: find the ACTUAL onset condition for E_2(mu_n) excess over 3n^2-3n.
The prior worker claimed trigger = "2^n < p fails". Probe 1 REFUTED that:
  (786433,16): 2^n<p TRUE  but excess=0
  (786433,64): 2^n<p FALSE but excess=0
  (786433,256):2^n<p FALSE but excess=0
So 2^n<p is not it. Hypothesis: excess>0  <=>  q < (something like) n^2 * const, i.e.
the multiplicative set's sumset {a+b : a,b in mu_n} starts to OVERFLOW / collide because
|mu_n + mu_n| <= min(n(n+1)/2 distinct sums, p). When the generic sumset size ~ n^2/2 is
forced to collide (either by wrap mod p, or by the multiplicative structure pinching sums
into fewer residues than n^2/2), energy rises above baseline.

Probe: for each cell print n, p, beta, the integer-sumset size |S+S|_Z, the mod-p sumset size
|S+S|_Fp, n(n+1)/2 (max distinct unordered sums), and excess. Find what predicts excess>0.
"""
import sympy, math

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    assert len(S) == n
    return sorted(S)

def energies(S, p):
    from collections import Counter
    cZ, cF = Counter(), Counter()
    for a in S:
        for b in S:
            cZ[a+b] += 1
            cF[(a+b) % p] += 1
    eZ = sum(v*v for v in cZ.values())
    eF = sum(v*v for v in cF.values())
    return eZ, eF, len(cZ), len(cF)

print(f"{'p':>8} {'n':>5} {'beta':>5} {'q/n^2':>7} {'|S+S|Z':>7} {'|S+S|p':>7} {'maxsum':>7} {'EXC':>9} {'exc>0':>6}")
print("-"*80)
cells = []
for p in [193,257,769,3457,7681,12289,40961,65537,786433,7340033]:
    if not sympy.isprime(p): continue
    for a in range(3, 12):
        n = 2**a
        if (p-1) % n == 0 and n < p:
            cells.append((p,n))
for p,n in cells:
    S = subgroup(p,n)
    eZ,eF,szZ,szF = energies(S,p)
    base = 3*n*n-3*n
    exc = eF - base
    maxsum = n*(n+1)//2 + n  # number of distinct unordered+ordered diag sums upper bound ~ n(n-1)/2+n
    beta = math.log(p)/math.log(n)
    print(f"{p:>8} {n:>5} {beta:>5.2f} {p/(n*n):>7.2f} {szZ:>7} {szF:>7} {n*n:>7} {exc:>9} {str(exc>0):>6}")
print()
print("Looking for the threshold in q/n^2 (or beta) that separates exc=0 from exc>0.")
