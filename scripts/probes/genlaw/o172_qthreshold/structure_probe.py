#!/usr/bin/env python3
"""
Structure probe: for a given monomial pair (x^e,x^f) at deep band a0=r+1, pin k=r-1,
enumerate the alignable a0-subsets S, the bad scalars gamma=-e1(S), and tabulate
the value->multiplicity so we can see the analytic structure (which S contribute and
how many distinct gamma values result).

Faithful BabyBear prime p; exact integer (modular) arithmetic.
Reuses the residual-determinant alignedness test (ground truth, OwnershipBound.residual).
"""
import sys
from math import comb
from itertools import combinations

p = 2013265921  # BabyBear

def mu_n(n):
    e = (p-1)//n
    for c in range(2, 400):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return [pow(h, i, p) for i in range(n)]
    raise RuntimeError("no root")

def detm(M):
    m = len(M)
    M = [row[:] for row in M]
    det = 1
    for col in range(m):
        piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = (-det) % p
        det = (det * M[col][col]) % p
        inv = pow(M[col][col], p-2, p)
        for rr in range(col+1, m):
            if M[rr][col] % p:
                f = (M[rr][col] * inv) % p
                M[rr] = [(M[rr][c] - f*M[col][c]) % p for c in range(m)]
    return det

def residual(dom, k, t, y):
    # (k+1)x(k+1) bordered Vandermonde, t = tuple of node indices, y = witness vals on dom
    m = k+1
    M = []
    for a in range(m):
        row = [pow(dom[t[a]], b, p) for b in range(k)]
        row.append(y[t[a]] % p)
        M.append(row)
    return detm(M)

def aligned_gamma(dom, k, S, u0, u1):
    """Return (aligned, gamma_or_None). gamma=-r0/r1 consistent over all (k+1)-subtuples."""
    gam = None
    nondeg = False
    any_u1 = False
    for t in combinations(S, k+1):
        r0 = residual(dom, k, t, u0)
        r1 = residual(dom, k, t, u1)
        if r0 or r1:
            nondeg = True
        if r1 == 0:
            if r0 != 0:
                return (False, None)
        else:
            any_u1 = True
            g = ((-r0) * pow(r1, p-2, p)) % p
            if gam is None:
                gam = g
            elif gam != g:
                return (False, None)
    if not nondeg:
        return (False, None)
    return (True, gam if any_u1 else None)

def probe(n, r, e, f):
    dom = mu_n(n)
    k = r-1
    a0 = r+1
    u0 = [pow(x, e, p) for x in dom]
    u1 = [pow(x, f, p) for x in dom]
    badvals = {}   # gamma -> count of contributing subsets
    nsets = 0
    for S in combinations(range(n), a0):
        ok, gam = aligned_gamma(dom, k, S, u0, u1)
        if ok and gam is not None:
            nsets += 1
            badvals[gam] = badvals.get(gam, 0) + 1
    nbad = len(badvals)
    # multiplicity histogram
    mult = {}
    for g, c in badvals.items():
        mult[c] = mult.get(c, 0) + 1
    print(f"n={n} r={r} a0={a0} k={k} stack=(x^{e},x^{f}): #bad={nbad}  #contrib_sets={nsets}  K={(1<<r)*comb(n//2,r)}")
    print(f"   multiplicity histogram (sets-per-gamma -> #gammas): {dict(sorted(mult.items()))}")
    # how many gammas equal 0?
    if 0 in badvals:
        print(f"   gamma=0 present, owns {badvals[0]} sets")
    return nbad, nsets, badvals

if __name__ == "__main__":
    # usage: structure_probe.py n  r1 e1 f1  r2 e2 f2  ...
    n = int(sys.argv[1])
    rest = [int(x) for x in sys.argv[2:]]
    for i in range(0, len(rest), 3):
        r, e, f = rest[i], rest[i+1], rest[i+2]
        probe(n, r, e, f)
