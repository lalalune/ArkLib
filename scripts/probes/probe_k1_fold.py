#!/usr/bin/env python3
"""K1 (issue #357 §5): is the KKH26 bad line fold-invariant down the smooth tower?
Bad line at level μ ↔ r-subset S of G_μ = 2^μ-th roots of unity; bad scalar = -ΣS.
Fold x↦x² : G_μ → G_{μ-1} (2-to-1, collapses antipodal pairs a,-a since (-a)²=a²).
HYPOTHESIS (K1): fold STRICTLY shrinks the bad family — S containing an antipodal pair maps to
<r elements ⟹ no longer a valid r-subset bad line ⟹ that bad line dies. Pre-registered falsifier:
if EVERY r-subset survives (no antipodal collapse), K1 dies (fold-invariant)."""
import itertools, math
def subgroup(p,s):
    if (p-1)%s: return None
    g=None
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//s,p); return sorted({pow(h,i,p) for i in range(s)})
def antipodal_pairs(p,G):
    Gs=set(G); return {frozenset((a,(-a)%p)) for a in G if (-a)%p in Gs and a!=(-a)%p}
print(f"{'p':>6} {'s=2^μ':>6} {'r':>3} {'#r-subsets':>11} {'fold-survivors':>14} {'killed':>7} {'strict?':>8}")
for (p,mu,r) in [(17,3,2),(17,3,3),(97,4,2),(97,4,3),(97,4,4),(193,5,3),(193,5,4),(257,4,4)]:
    s=2**mu; G=subgroup(p,s)
    if G is None or len(G)!=s: continue
    sq={}  # element -> square
    for a in G: sq[a]=(a*a)%p
    total=0; survivors=0
    for S in itertools.combinations(G,r):
        total+=1
        # fold survives iff squares are all distinct (no antipodal collapse)
        sqs={sq[a] for a in S}
        if len(sqs)==r: survivors+=1
    killed=total-survivors
    print(f"{p:>6} {s:>6} {r:>3} {total:>11} {survivors:>14} {killed:>7} {str(killed>0):>8}")
