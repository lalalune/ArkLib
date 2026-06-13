#!/usr/bin/env python3
"""probe_quartic_powersum_census.py (#389, Fable): the additive power-word deep-band census.
#{4-subsets of mu_n : sum x = sum x^2 = 0} = n/4 (the mu_4-cosets {g,gi,-g,-gi}), q-INDEPENDENT
(n=8->2,16->4,32->8 across q). Verified cores==mu_4-cosets on mu_16. The k=2 power-word ladder
#{(m+3)-subsets: p_1..p_{m+1}=0} on mu_16 fires ONLY at m=1 (n/4); m=0,2,3 = 0 (vanishing-
power-sum subsets must be <zeta>-coset unions, Lam-Leung; size-4 mu_4-coset is the only
realizable one below 8). The m=1 analogue of cubicSupply=C(n,2)/3. The incomplete Gauss sum
#{X^4+bX+c split in mu_n} collapses to this exact coset count over 2-power mu_n via antipodal
closure (in-tree subset_neg_mem_of_sum_zero)."""
from itertools import combinations
def rou(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return [pow(h,i,p) for i in range(n)]
def census(D,p,asize,mc):
    return sum(1 for T in combinations(range(len(D)),asize)
               if all(sum(pow(D[t],d,p) for t in T)%p==0 for d in range(1,mc+1)))
if __name__=="__main__":
    for n in (8,16,32):
        for p in ([17,97,193] if n<=16 else [97,193,353]):
            if (p-1)%n: continue
            D=rou(p,n)
            print(f"n={n} q={p}: #4-subsets(sum=sum2=0)={census(D,p,4,2)}  (n/4={n//4})")
    print("ladder on mu_16 q=193:", {m: census(rou(193,16),193,m+3,m+1) for m in range(4)})
