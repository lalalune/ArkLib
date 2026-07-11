#!/usr/bin/env python3
"""probe_subgroup_additive_energy.py (#389, Fable): EXACT additive energy of a multiplicative
subgroup mu_n in the large-q (Lam-Leung) regime.

E_2(mu_n) = #{(a,b,c,d) in mu_n^4 : a+b=c+d}.  Via Lam-Leung/Mann (vanishing sums of n-th roots
of unity decompose into the cyclotomic-prime minimal relations; for 2-power n, antipodal pairs
{x,-x}), the 4-term relation a+b-c-d=0 forces antipodal/trivial structure, giving EXACTLY:
  E_2(mu_n) = 3n^2 - 3n   for EVEN n  (contains -1: trivial perms 2n^2 + zero-sum class n^2 - corr),
  E_2(mu_n) = 2n^2 -  n   for ODD  n  (no -1: pure Sidon, trivial perms only).
Verified even n=4,6,8,10,12,16,32 -> 3n(n-1); odd n=3,5,9 -> n(2n-1). Holds for q above a
moderate poly threshold (q ~ n^2; n=16 clean at q>=1153); small-q inflation below.
SIGNIFICANCE: sharpens the literature bound E << n^{5/2} to an EXACT formula -- mu_n is
MINIMAL-additive-energy (Sidon-like), which is WHY delta*(smooth) ~ delta*(random) ~ capacity.
The prize gap Theta(1/log n) lives in the HIGHER moments E_r (r>=4), where the clean
(2r-1)!!-Gaussian/antipodal pattern BREAKS (E_4 leading ~147 != 7!!=105, inclusion-exclusion
among antipodal matchings) -- that is the open sum-product wall."""
from collections import Counter
import sympy
def rou(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return [pow(h,i,p) for i in range(n)]
def E2(D,p):
    c=Counter()
    for a in D:
        for b in D: c[(a+b)%p]+=1
    return sum(v*v for v in c.values())
if __name__=="__main__":
    for n in [4,6,8,10,12,16,32,3,5,9]:
        q=n*n*n
        while not(sympy.isprime(q) and (q-1)%n==0): q+=1
        e=E2(rou(q,n),q)
        pred=3*n*(n-1) if n%2==0 else 2*n*n-n
        print(f"n={n:3d} q={q}: E_2={e:6d}  pred({'even 3n(n-1)' if n%2==0 else 'odd n(2n-1)'})={pred:6d}  {'MATCH' if e==pred else 'diff'}")
