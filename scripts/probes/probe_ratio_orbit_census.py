#!/usr/bin/env python3
"""Orbit-class census of monomial bad sets (#371, follow-up to the gamma-coset fibration).

The fibration theorem (MonomialGammaFibration.lean) says badSet(X^a, X^b) \\ {0} is a
union of free <c>-orbits, c = g^(b-a).  This probe measures the ORBIT-CLASS COUNT
as a function of (a, b, d, threshold) hunting for a law: class count vs
gcd(b-a, n), 2-adic structure, and the spectrum mechanism.

Exploratory census (not pre-registered as pass/fail except the fibration assertions,
which re-verify): outputs the class-count table.
"""

import itertools
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
from math import gcd

def inv(x, p):
    return pow(x, p - 2, p)

def smooth_domain(p, n):
    for g in range(2, p):
        if pow(g, n, p) == 1:
            if all(pow(g, n // q, p) != 1 for q in (2, 3, 5, 7) if n % q == 0):
                return g, [pow(g, i, p) for i in range(n)]
    raise ValueError

def fits(points, vals, d, p):
    m = len(points)
    if m <= d + 1:
        return True
    base, bv = points[: d + 1], vals[: d + 1]
    def ev2(x):
        tot = 0
        for j in range(d + 1):
            num = den = 1
            for k2 in range(d + 1):
                if k2 != j:
                    num = num * ((x - base[k2]) % p) % p
                    den = den * ((base[j] - base[k2]) % p) % p
            tot = (tot + bv[j] * num * inv(den % p, p)) % p
        return tot
    return all(ev2(points[i]) == vals[i] % p for i in range(d + 1, m))

def bad_set(dom_pts, u0, u1, d, t, p, n):
    bad = set()
    subsets = list(itertools.combinations(range(n), t))
    for gam in range(p):
        line = [(u0[i] + gam * u1[i]) % p for i in range(n)]
        for S in subsets:
            if not fits([dom_pts[i] for i in S], [line[i] for i in S], d, p):
                continue
            if fits([dom_pts[i] for i in S], [u0[i] for i in S], d, p) and \
               fits([dom_pts[i] for i in S], [u1[i] for i in S], d, p):
                continue
            bad.add(gam)
            break
    return bad

for (p, n) in ((17, 8), (97, 8), (97, 16)):
    g, dom_pts = smooth_domain(p, n)
    print(f"=== (p, n) = ({p}, {n}), g = {g}")
    for d in (1, 2):
        t = d + 2  # boundary threshold
        rows = []
        for delta in range(1, n):
            for a in (0, 1, 2, d, d + 1):
                b = a + delta
                if b >= n:
                    continue
                u0 = [pow(x, a, p) for x in dom_pts]
                u1 = [pow(x, b, p) for x in dom_pts]
                c = pow(g, delta, p)
                ordc = n // gcd(n, delta)
                B = bad_set(dom_pts, u0, u1, d, t, p, n)
                nz = len(B - {0})
                assert nz % ordc == 0, f"FIBRATION VIOLATED {(p,n,d,a,b)}"
                rows.append((a, b, delta, gcd(n, delta), ordc,
                             nz // ordc, nz, 0 in B))
        # print compact: group by (delta-gcd, class count)
        print(f"  d={d} t={t}:  (a,b) Δ gcd ord classes nz zero∈B")
        for r in rows:
            print(f"    ({r[0]},{r[1]}) Δ={r[2]} gcd={r[3]} ord={r[4]} "
                  f"classes={r[5]} nz={r[6]} z={r[7]}")
print("census complete")
