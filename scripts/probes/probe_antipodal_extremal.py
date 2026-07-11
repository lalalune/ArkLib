#!/usr/bin/env python3
"""VERIFY workflow claim: is max_c L_t(c) = 2^{μ-1} (t=2), 2^{μ-1}-1 (t=3) for μ_n, via the antipodal
family? L_t(c)=#{S⊆μ_n,|S|=SIZE, power sums p_1..p_t(S)=c}. Test BOTH size conventions (SIZE=k+t and
SIZE=t+something) and report max_c L_t + whether the antipodal extremizer holds. Independent check."""
import itertools, math
from collections import Counter
def subgroup(p,n):
    if (p-1)%n: return None
    g=None
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})
def maxLt(p,D,size,t):
    cnt=Counter()
    for S in itertools.combinations(D,size):
        ps=tuple(sum(pow(x,j,p) for x in S)%p for j in range(1,t+1))
        cnt[ps]+=1
    return max(cnt.values()), max(cnt, key=cnt.get)
print(f"{'p':>5} {'n=2^μ':>6} {'2^(μ-1)':>8} {'t':>2} {'size':>5} {'max_c L_t':>10} {'= 2^(μ-1)?':>11}")
for (p,mu) in [(17,3),(97,4),(193,5),(257,4)]:
    n=2**mu; D=subgroup(p,n)
    if D is None or len(D)!=n: continue
    half=2**(mu-1)
    for t in [2,3]:
        for size in [t+1, t+2]:  # try a few subset sizes
            if size>n: continue
            mx,argc=maxLt(p,D,size,t)
            tag = "YES" if mx==half-(t-2) else ("="+str(mx))
            print(f"{p:>5} {n:>6} {half:>8} {t:>2} {size:>5} {mx:>10} {tag:>11}")
