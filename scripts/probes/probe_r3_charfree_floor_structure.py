#!/usr/bin/env python3
"""
PROBE 10: identify the char-free guaranteed-family structure for E_3 (r=3 additive energy),
generalizing T1/T2/T3 at r=2. E_3(S) = #{(v,w) in (S^3)^2 : v1+v2+v3 = w1+w2+w3}.
For a generic set (no extra additive coincidences) the energy comes only from w being a
PERMUTATION of v (6 perms of 3 elements, with overlaps when entries coincide). For a
NEGATION-CLOSED set there are EXTRA guaranteed solutions from cancellation a+(-a)=0.
GOAL: find the clean near-Sidon closed form (the floor) and the guaranteed families.

E_3 near-Sidon target from probe 9: E_3/n^3 = 10.000 at n=8 -> E_3 = 10 n^3? check at n=8:
10*512 = 5120 = observed. So near-Sidon E_3 = 10 n^3 + lower-order? Let's fit exactly.
"""
import sympy
from itertools import product, permutations
from collections import Counter

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def Er(S,p,r):
    c=Counter()
    for v in product(S,repeat=r): c[sum(v)%p]+=1
    return sum(x*x for x in c.values())

# fit E_3 near-Sidon (small n, no excess) as polynomial in n
# use cells where excess is 0 (near-Sidon): small n relative to p
cells=[(7681,8),(40961,8),(786433,8),(786433,16),(786433,32),(7340033,8),(7340033,16)]
print("near-Sidon E_3 samples (excess-free cells):")
pts=[]
for p,n in cells:
    if (p-1)%n: continue
    if n**3>300000: continue
    S=subgroup(p,n); e=Er(S,p,3)
    # check near-Sidon by comparing to a known no-excess proxy: E_2==3n^2-3n
    e2=Er(S,p,2)
    sidon = (e2==3*n*n-3*n)
    print(f"  p={p} n={n}: E_3={e} sidon(r2)={sidon} E_3/n^3={e/n**3:.4f}")
    if sidon: pts.append((n,e))

# fit cubic a n^3 + b n^2 + c n + d through near-Sidon points
if len(pts)>=4:
    import numpy as np
    ns=[x[0] for x in pts]; es=[x[1] for x in pts]
    A=np.array([[n**3,n**2,n,1] for n in ns],dtype=float)
    coef,_,_,_=np.linalg.lstsq(A,np.array(es,dtype=float),rcond=None)
    print(f"  cubic fit E_3 ~ {coef[0]:.2f} n^3 + {coef[1]:.2f} n^2 + {coef[2]:.2f} n + {coef[3]:.2f}")
print()
print("guaranteed families for E_3 (char-free), negation-closed:")
print(" perm family: w a permutation of v (<=6 per v); plus antipodal-cancellation families.")
print(" The clean FLOOR brick = the diagonal v=w alone gives n^3 (char-free, trivial, like T1).")
print(" A richer floor needs the perm+antipodal inclusion-exclusion (heavier).")
