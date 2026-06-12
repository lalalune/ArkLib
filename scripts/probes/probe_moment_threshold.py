#!/usr/bin/env python3
"""NOVEL framing (issue #357): δ* via the moment-threshold / structured-excess decomposition.
L_t(c) = #{S⊆μ_n : |S|=k+t, power sums p_1..p_t = c} (= e_1..e_t prescribed, Newton). Expected
(random c) = C(n,k+t)/q^t. Structured excess = max_c L_t - expected. Verify: (a) the Newton
equivalence e_j<->p_j; (b) the expected count C(n,k+t)/q^t numerically (avg of L_t over c); (c) whether
smooth domains show EXCESS (max_c L_t > expected) — the KKH26 mechanism — vs random domains."""
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
def Lt_dist(p,D,size,t):
    # distribution of L_t(c) over c=(p_1,...,p_t); return Counter of c-tuples
    cnt=Counter()
    for S in itertools.combinations(D,size):
        ps=tuple(sum(pow(x,j,p) for x in S)%p for j in range(1,t+1))
        cnt[ps]+=1
    return cnt
print("NOVEL moment-threshold framing — expected vs structured excess (smooth vs random):")
print(f"{'p':>5} {'n':>4} {'k+t':>4} {'t':>2} {'C(n,k+t)':>9} {'q^t':>8} {'expected':>9} {'max_c L_t':>10} {'excess?':>8} {'dom'}")
for (p,n,k,t,dom) in [(17,8,2,1,'smooth'),(17,8,2,1,'random'),(17,8,2,2,'smooth'),(17,8,2,2,'random'),
                      (41,8,2,1,'smooth'),(41,8,2,1,'random'),(41,8,2,2,'smooth'),(41,8,2,2,'random')]:
    if dom=='smooth':
        D=subgroup(p,n)
        if D is None or len(D)!=n: continue
    else:
        import random; random.seed(3); D=sorted(random.sample(range(1,p),n))
    size=k+t
    dist=Lt_dist(p,D,size,t)
    Cnt=math.comb(n,size); qt=p**t; exp=Cnt/qt; mx=max(dist.values())
    print(f"{p:>5} {n:>4} {size:>4} {t:>2} {Cnt:>9} {qt:>8} {exp:>9.3f} {mx:>10} {str(mx>exp*1.5):>8} {dom}")
