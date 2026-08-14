#!/usr/bin/env python3
"""
FOLLOW-UP PROBE: is (e_1, e_2, e_5) ALONE enough to force the unordered quintuple of n-th roots of
unity?  The first sweep showed 0 collisions for (e_1,e_2,e_5) at n=5,6,8,10, AND both conjugation
identities e_4 = e_5 conj(e_1) and e_3 = e_5 conj(e_2) are exact. If both hold, then (e_1,e_2,e_5)
determines (e_3,e_4) hence all five esymm hence the monic quintic hence the unordered quintuple.

Decisive: larger n + tighter multiset key + explicit determination check.
Counter-check: is (e_1, e_5) alone (the bare sum+product) enough? expect NO (e_2 underdetermined).
"""
import itertools, math, cmath
TOL = 1e-7

def esymm(xs):
    e = [0]*6; e[0]=1.0
    for x in xs:
        for k in range(5,0,-1):
            e[k]=e[k]+e[k-1]*x
    return e[1],e[2],e[3],e[4],e[5]

def roots(n):
    return [cmath.exp(2j*math.pi*t/n) for t in range(n)]

def k(z):
    return (round(z.real/TOL), round(z.imag/TOL))

def mk(xs):
    return tuple(sorted(k(x) for x in xs))

for n in (8, 12, 16):
    R = roots(n)
    all5 = list(itertools.combinations_with_replacement(range(n), 5))
    b125 = {}
    b15 = {}
    for c in all5:
        xs=[R[i] for i in c]
        e1,e2,e3,e4,e5=esymm(xs)
        b125.setdefault((k(e1),k(e2),k(e5)), set()).add(mk(xs))
        b15.setdefault((k(e1),k(e5)), set()).add(mk(xs))
    col125 = sum(len(v)-1 for v in b125.values() if len(v)>1)
    col15  = sum(len(v)-1 for v in b15.values() if len(v)>1)
    print(f"n={n:3d} #5mult={len(all5):6d}  (e1,e2,e5)extra-coll={col125:5d}  (e1,e5)extra-coll={col15:6d}")
print("If (e1,e2,e5)=0 across n: the 5-element rung needs only e_1,e_2,e_5 (e_3,e_4 both free).")
