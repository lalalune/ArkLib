#!/usr/bin/env python3
"""
Probe: does NEGATION-CLOSURE (forall x in G, -x in G) buy a clean all-r floor on
rEnergy(G,r) ABOVE the hypothesis-free swap floor 2n^r - n^{r-1}?

At r=2 the negation-closed floor is 3n^2 - 3n (diagonal T1 + swap T2 + antipodal T3),
i.e. n^{r-1} MORE than the swap floor 2n^2 - n.

Candidate all-r third family (needs -x in G): "ANTI01" - flip the SIGN of coordinates 0,1
of v to get w, AND require those two coords to be negatives so the sum is preserved? No -
sign-flipping coords 0,1 changes sum by -2(v0+v1), preserved only if v0+v1=0, i.e. v1=-v0.

Cleaner candidate matching the r=2 T3 = {(a,-a,c,-c)}: the energy quadruple (v,w) where
w = (-v1, -v0, v2, v3, ..., v_{r-1})  [swap coords 0,1 AND negate them].
Then sum w = -v1 - v0 + v2 + ... = sum v - 2(v0+v1) + ... wait recompute:
sum w = (-v1) + (-v0) + v2 + ... + v_{r-1} = sum v - v0 - v1 - v1 - v0 ... no.
sum v = v0+v1+v2+...; sum w = -v1-v0+v2+... = sum v - 2v0 - 2v1. Preserved iff v0+v1=0.

So ANTI01 only preserves sum on the slice v1 = -v0. On that slice it gives NEW solutions
(distinct from diagonal/swap when v0 != 0 and v0 != v1 etc). Count the resulting floor and
test if rEnergy - (swap floor) >= (this antipodal contribution), and whether it's a clean
closed form (expect ~ n^{r-1} like r=2's extra 3n^2-3n - (2n^2-n) = n^2-2n... let's just measure).
"""
import itertools
from collections import Counter

def rEnergy(G, r):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v)] += 1
    return sum(c*c for c in cnt.values())

def floor_diag_swap_anti01(G, r):
    """count distinct (v,w): w=v, w=swap01(v), or w=anti01(v) (the latter only when sum preserved)."""
    seen = set()
    for v in itertools.product(G, repeat=r):
        sv = sum(v)
        seen.add((v, v))                       # diagonal
        if r >= 2:
            sw = (v[1], v[0]) + v[2:]           # swap01
            if sum(sw) == sv:                  # always true
                seen.add((v, sw))
            an = (-v[1], -v[0]) + v[2:]         # anti01 (negate the swapped pair)
            if sum(an) == sv:                  # only when v0+v1=0
                # need an entries in G; for negation-closed G with integers symmetric this holds
                if all(x in G for x in an):
                    seen.add((v, an))
    return len(seen)

if __name__ == "__main__":
    # negation-closed integer sets symmetric about 0
    print("negation-closed G = {-k..k}\\{0} style, n even")
    print("n  r | diag_swap_anti01  swapFloor(2n^r-n^{r-1})  rEnergy | extra=floor-swap")
    for halfk in [1,2,3]:
        G = [x for x in range(-halfk, halfk+1) if x != 0]  # symmetric, 0 excluded
        n = len(G)
        for r in [2,3,4]:
            fl = floor_diag_swap_anti01(G, r)
            sw = 2*n**r - n**(r-1)
            re = rEnergy(G, r)
            print(f"{n}  {r} | {fl:8d}  {sw:8d}  {re:8d} | extra={fl-sw}, floor<=rE:{fl<=re}")
    print()
    print("r=2 check: 3n^2-3n vs measured floor on symmetric G")
    for halfk in [1,2,3,4]:
        G = [x for x in range(-halfk, halfk+1) if x != 0]
        n=len(G)
        fl = floor_diag_swap_anti01(G,2)
        print(f"  n={n}: floor={fl}, 3n^2-3n={3*n*n-3*n}, match={fl==3*n*n-3*n}")
