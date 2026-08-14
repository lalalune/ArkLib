#!/usr/bin/env python3
"""Probe: the Schur-vanishing locus {R' : [R']x^b = 0} (= h_{b-k}(R')=0, the bad-alpha /
unified-open-core K carrier) is rotation-invariant on mu_n: R' in vanishing-set <=> zeta*R' in
vanishing-set. Direct corollary of the homogeneity dd(c*v,b) = c^{b-(#s-1)} dd(v,b): with c=zeta
a unit, dd(zeta*v,b) = 0 <=> dd(v,b) = 0.

NEVER validate at n=q-1: pure char-0 / complex algebraic identity over mu_n roots of unity.
"""
import cmath, random

def dd(vals, b):
    s = len(vals)
    tot = 0j
    for i in range(s):
        num = vals[i] ** b
        den = 1 + 0j
        for j in range(s):
            if j != i:
                den *= (vals[i] - vals[j])
        tot += num / den
    return tot

random.seed(7)
print("=== Schur-vanishing locus is rotation-invariant: [R']x^b=0 <=> [zeta R']x^b=0 on mu_n ===")
ok = True
vanish_hits = 0
checked = 0
for n in [8, 16, 32]:
    roots = [cmath.exp(2j * cmath.pi * t / n) for t in range(n)]
    zeta = cmath.exp(2j * cmath.pi / n)
    for trial in range(4000):
        k = random.randint(1, 3)
        sub = random.sample(range(n), k + 1)
        R = [roots[t] for t in sub]
        b = random.randint(k + 1, k + 7)
        d0 = dd(R, b)
        Rz = [zeta * x for x in R]
        dz = dd(Rz, b)
        van0 = abs(d0) < 1e-7
        vanz = abs(dz) < 1e-7
        checked += 1
        if van0:
            vanish_hits += 1
        if van0 != vanz:
            ok = False
            print("FAIL (invariance broken)", n, k, b, sub, abs(d0), abs(dz))
            break
    if not ok:
        break
print("rotation-invariance of vanishing locus:",
      "ALL MATCH" if ok else "FAILED",
      f"({checked} checked, {vanish_hits} actual vanishings observed)")
