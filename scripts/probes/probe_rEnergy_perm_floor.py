#!/usr/bin/env python3
"""
Probe: the PERMUTATION floor for the r-fold additive energy rEnergy(G,r).

rEnergy(G,r) = #{(v,w) in (G^r)^2 : sum v = sum w}.

The "trivial" energy solutions are w = v o sigma for sigma in Sym(r) (same multiset of
coordinates => same sum). Question: is

    PermFloor(G,r) := #{(v,w) : w_i = v_{sigma(i)} for some sigma in Sym_r}

(a) always <= rEnergy(G,r)  [it is, by construction: every such (v,w) has sum v = sum w]
(b) a CLEAN closed form?  For GENERIC v (all coords distinct), the orbit {v o sigma} has
    size r!, so the pair count is sum_v |{w : w perm of v}|.

We want a HYPOTHESIS-FREE lower bound. The cleanest sub-floor that needs no genericity:
the DIAGONAL (sigma=id) gives |G|^r (already proven). Adding the full permutation orbit
overcounts when v has repeated coords. So the honest clean lower bound from permutations is

    rEnergy(G,r) >= #{(v,w) : w perm of v} = sum_{v in G^r} (#distinct permutations of v).

We test: is sum_v (#distinct perms of v) a clean closed form in |G|=n and r? And is it
always <= rEnergy? (yes trivially). Also compare to the r=2 antipodal floor 3n^2-3n (NOTE:
antipodal is NOT a permutation symmetry; it is a SIGN symmetry needing negation-closure -
so the permutation floor and the antipodal floor are DIFFERENT mechanisms; permutation is
hypothesis-FREE, antipodal needs -x in G).
"""
import itertools
from collections import Counter
from math import factorial

def rEnergy_bruteforce(G, r):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v)] += 1
    return sum(c*c for c in cnt.values())

def perm_floor(G, r):
    # sum over v of (# distinct permutations of v as an r-tuple)
    total = 0
    for v in itertools.product(G, repeat=r):
        mult = Counter(v)
        denom = 1
        for m in mult.values():
            denom *= factorial(m)
        total += factorial(r) // denom
    return total

def perm_floor_closed(n, r):
    # closed form for sum_v (# distinct perms): this counts ordered pairs (v,w)
    # with w a permutation of v = #{(v,w): v,w in G^r, w sorts to same multiset as v}
    # = sum over multisets M of size r from G of (#orderings)^2
    # We compute it directly as a check via multisets.
    from itertools import combinations_with_replacement
    total = 0
    for combo in combinations_with_replacement(range(n), r):
        mult = Counter(combo)
        denom = 1
        for m in mult.values():
            denom *= factorial(m)
        orderings = factorial(r)//denom
        total += orderings*orderings
    return total

if __name__ == "__main__":
    print("n  r | permFloor  permClosed  rEnergy(intG)  |G|^r  | permFloor<=rEnergy?")
    for n in [3,4,5,6]:
        G = list(range(n))  # integers - no wraparound, generic additive structure
        for r in [2,3,4]:
            pf = perm_floor(G, r)
            pc = perm_floor_closed(n, r)
            re = rEnergy_bruteforce(G, r)
            diag = n**r
            ok = pf <= re
            print(f"{n}  {r} | {pf:9d}  {pc:9d}  {re:11d}  {diag:6d} | {ok}  (perm==closed: {pf==pc})")
    print()
    print("Check r=2 perm floor == 2n^2 - n  (diagonal n^2 + swap n^2 - overlap n):")
    for n in [3,4,5,6,7]:
        G=list(range(n))
        pf = perm_floor(G,2)
        print(f"  n={n}: permFloor(r=2)={pf}, 2n^2-n={2*n*n-n}, match={pf==2*n*n-n}")
