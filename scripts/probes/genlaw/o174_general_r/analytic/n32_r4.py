# n=32, r=4 (a=5): get a defensible UPPER estimate on #bad. Since exact phi unknown, use the WIDEST
# plausible slice that still reproduces n=16 within the candidate. We measure two anchors:
#  (i) p2=0 slice distinct-e1 (the homogeneous slice; matched r=3 at n=16) -> gives a comparable magnitude.
#  (ii) full spectrum (hard upper bound on #bad, but overshoots K).
# Report whether K/2 dominates the p2=0 anchor at n=32 r=4,5 as a sanity gate.
from itertools import combinations
import math
p=2013265921
def gen_order(p,n):
    for g in range(2,500):
        cand=pow(g,(p-1)//n,p)
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
            return cand
n=32
g=gen_order(p,n); H=[pow(g,i,p) for i in range(n)]; Hsq=[pow(h,2,p) for h in H]
assert len(set(H))==n
for a in [5,6]:  # r=4,5
    r=a-1
    e1set=set(); cnt=0
    for S in combinations(range(n),a):
        if sum(Hsq[i] for i in S)%p==0:
            e1set.add(sum(H[i] for i in S)%p); cnt+=1
    K=2**r*math.comb(16,r)
    print(f"n=32 r={r} a={a}: p2=0 slice configs={cnt} distinct-e1={len(e1set)}  K={K} K/2={K//2}  e1<=K/2? {len(e1set)<=K//2}")
