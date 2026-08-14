# Verify: #spurious(antipodal-free, sum u=sum u^3=0) ~= #configs/p^2 ?
# And does the threshold (spurious appear iff p <~ sqrt(#configs)) hold?
# If yes, then at delta* (N0 ~ eps* q), #configs~N0^2 => #spurious~eps*^2 << 1 => CLOSURE.
import numpy as np
from itertools import combinations
from sympy import primerange
from math import comb

def count_spurious(n, size, p):
    HALF=n//2
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    mu=[pow(g,j,p) for j in range(n)]
    spur=0
    for S in combinations(range(n),size):
        if any(((j+HALF)%n) in set(S) for j in S): continue   # antipodal-free
        us=[mu[j] for j in S]
        if sum(us)%p!=0: continue
        if sum(pow(u,3,p) for u in us)%p!=0: continue
        spur+=1
    return spur

def n_antipodalfree(n,size):
    HALF=n//2
    return comb(HALF,size)*(2**size)

for (n,size) in [(16,6),(16,8),(32,6)]:
    NC=n_antipodalfree(n,size)
    print(f"\nn={n} size={size}: #antipodal-free configs = {NC}, sqrt={NC**0.5:.0f}")
    for p in list(primerange(n+1, 2000)):
        if p%n!=1: continue
        s=count_spurious(n,size,p)
        if s is None: continue
        pred=NC/p**2
        print(f"  p={p}: actual spurious={s}, predicted #configs/p^2={pred:.2f}, ratio={s/pred if pred>0 else 0:.2f}")
