#!/usr/bin/env python3
"""K4 zero-slack census check (issue #357 §5, mutually-falsifying with K1).
Bad scalars = distinct r-subset sums of G_μ (2^μ-th roots of unity mod p). The bad line is
'census-extremal / zero-slack' if its bad-scalar count saturates the maximal possible (C(s,r), all
sums distinct). SLACK = C(s,r) - #distinct-sums. K1 (fold improvement) requires SLACK>0 (room to
exploit); if SLACK=0 (census-extremal) K1 dies. Pre-registered: since K1 SURVIVED its falsifier
(probe_k1_fold), expect SLACK>0 here (the two can't both hold)."""
import itertools, math
def subgroup(p,s):
    if (p-1)%s: return None
    g=None
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//s,p); return sorted({pow(h,i,p) for i in range(s)})
print(f"{'p':>6} {'s':>4} {'r':>3} {'C(s,r)':>8} {'#distinct sums':>14} {'slack':>7} {'slack>0?':>8}")
for (p,mu,r) in [(17,3,2),(17,3,3),(97,4,2),(97,4,3),(97,4,4),(193,5,3),(257,4,4),(193,5,4)]:
    s=2**mu; G=subgroup(p,s)
    if G is None or len(G)!=s: continue
    sums={sum(S)%p for S in itertools.combinations(G,r)}
    Csr=math.comb(s,r); nd=len(sums); slack=Csr-nd
    print(f"{p:>6} {s:>4} {r:>3} {Csr:>8} {nd:>14} {slack:>7} {str(slack>0):>8}")
