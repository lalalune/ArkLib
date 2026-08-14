#!/usr/bin/env python3
"""
PROBE 9: is there a clean CHAR-FREE lower bound (floor) for the r-fold additive energy
  E_r(S) = #{(v,w) in (S^r)^2 : sum v = sum w}
for negation-closed S, generalizing the r=2 floor 3n^2-3n? 
Guaranteed families for general r (char-free, like T1/T2/T3 at r=2):
 - DIAGONAL: v=w (any v):  n^r solutions.  -> floor n^r always.
 - For r=2 we got 3n^2-3n (extra from swap + antipodal). For general r the guaranteed
   count from permutation-of-w (w a permutation of v) is more complex.
Just MEASURE E_r and compare to candidate floors n^r, (r! ish), to see what a clean
char-free floor looks like, and whether it's worth a Lean brick. Focus r=2,3.
"""
import sympy
from itertools import product
from collections import Counter

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def Er(S, p, r):
    c = Counter()
    for v in product(S, repeat=r):
        c[sum(v)%p] += 1
    return sum(x*x for x in c.values())

for p,n,r in [(769,8,3),(769,16,3),(7681,8,3),(7681,16,3),(40961,16,3),(769,8,2),(769,16,2)]:
    if (p-1)%n: continue
    if n**r > 200000:  # cap compute
        print(f"p={p} n={n} r={r}: skipped (too big)"); continue
    S = subgroup(p,n)
    e = Er(S,p,r)
    # candidate char-free floors:
    diag = n**r
    print(f"p={p} n={n} r={r}: E_r={e}  n^r={diag}  E_r/n^r={e/diag:.3f}  "
          f"(r=2 ref floor 3n^2-3n={3*n*n-3*n if r==2 else '-'})")
print()
print("r=3: is there a clean closed-form char-free floor? If E_3/n^3 hugs a small constant")
print("with a clean combinatorial family, a higher-r char-free floor brick is viable.")
