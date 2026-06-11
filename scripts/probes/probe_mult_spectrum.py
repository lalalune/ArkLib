#!/usr/bin/env python3
"""N1 premise test: on a SMOOTH multiplicative subgroup vs random domain, compare the
#distinct (k+1)-subset SUMS (additive, governs bad count at jump per §10) vs
#distinct (k+1)-subset PRODUCTS (multiplicative twin). Fewer distinct = more collisions =
fewer bad scalars = the structure that could push the count BELOW the generic/Sidon ceiling.
Exact enumeration (combinatorial, fast)."""
import itertools
def subgroup(p,n):
    for cand in range(2,p):
        o=1;y=cand%p
        while y!=1:y=(y*cand)%p;o+=1
        if o==p-1:g=cand;break
    if (p-1)%n: return None
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})
def spectra(p,D,t):
    sums=set(); prods=set()
    for S in itertools.combinations(D,t):
        sums.add(sum(S)%p)
        pr=1
        for x in S: pr=(pr*x)%p
        prods.add(pr)
    from math import comb
    return len(sums), len(prods), comb(len(D),t)
import random
random.seed(7)
for (p,n,t) in [(13,6,3),(17,8,3),(41,8,3),(41,10,4),(97,12,4)]:
    sm=subgroup(p,n)
    if sm is None: print(f"p={p} n={n}: no subgroup"); continue
    ss,sp,C=spectra(p,sm,t)
    rd=sorted(random.sample(range(1,p),n)); rs,rp,_=spectra(p,rd,t)
    print(f"p={p} n={n} t={t} C(n,t)={C}: SMOOTH sums={ss} prods={sp} | RANDOM sums={rs} prods={rp}")
