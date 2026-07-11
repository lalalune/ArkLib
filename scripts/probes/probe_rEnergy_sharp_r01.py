#!/usr/bin/env python3
"""
PROBE 11: confirm the universal floor rEnergy G r >= |G|^r is SHARP (equality) at r=0,1.
r=0: (Fin 0 -> G) has exactly 1 element (empty function); sum=0=sum; rEnergy=1=|G|^0. OK.
r=1: rEnergy G 1 = #{(a,b) in G^2 : a=b} = |G| = |G|^1 (Sidon trivially at r=1). Verify.
r>=2: strict for any G with >=2 elements (swap family adds beyond diagonal). Verify gap.
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

def Er(S,p,r):
    if r==0: return 1
    c=Counter()
    for v in product(S,repeat=r): c[sum(v)%p]+=1
    return sum(x*x for x in c.values())

for p,n in [(769,8),(769,16),(7681,8)]:
    if (p-1)%n: continue
    S=subgroup(p,n)
    for r in [0,1,2]:
        e=Er(S,p,r); fl=n**r
        print(f"p={p} n={n} r={r}: rEnergy={e} |G|^r={fl} sharp={e==fl}")
print()
print("Expect: sharp (equality) at r=0 and r=1; strict at r=2.")
