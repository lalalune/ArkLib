# (A) Containment: every gap-valid e_m over F_p lands in the genuine C-sumset (reduced mod p)?
#     Tested where spurious configs provably exist (odd p == 1 mod n).
import numpy as np
from itertools import combinations
from sympy import primerange
from math import comb

def test(n, m, r, lo, hi):
    HALF=n//2; size=r*m; gap=[i for i in range(1,2*m) if i!=m]
    subs=list(combinations(range(n),size))
    needed=sorted(set(gap+[m]))
    M={i:np.zeros((len(subs),HALF),dtype=np.int64) for i in needed}
    for si,S in enumerate(subs):
        for i in needed:
            for c in combinations(S,i):
                T=sum(c)%n
                if T<HALF: M[i][si,T]+=1
                else: M[i][si,T-HALF]-=1
    # C-genuine e_m values (exact Z[zeta] vectors) = coset-union configs
    zmask=np.ones(len(subs),bool)
    for i in gap: zmask&=(M[i]==0).all(axis=1)
    C_em_vecs={tuple(row) for row in M[m][zmask]}   # exact sumset values in Z[zeta_n]
    def prim(p):
        e=(p-1)//n
        for a in range(2,p):
            g=pow(a,e,p)
            if pow(g,n,p)==1 and pow(g,n//2,p)==p-1: return g
    bad_primes=[]; nprime=0; sp_total=0
    for p in primerange(lo,hi):
        if p%n!=1: continue
        g=prim(p); nprime+=1
        powv=np.array([pow(g,l,p) for l in range(HALF)],dtype=np.int64)
        # genuine sumset reduced mod p
        Sigma_p=set(int((np.array(v)@powv)%p) for v in C_em_vecs)
        valid=np.ones(len(subs),bool)
        for i in gap: valid&=((M[i]@powv)%p==0)
        em_p=set(((M[m][valid]@powv)%p).tolist())
        spurious_valid = int(valid.sum()) - int(zmask.sum())  # extra configs over F_p
        sp_total += max(spurious_valid,0)
        if not em_p<=Sigma_p:
            bad_primes.append((p,sorted(em_p-Sigma_p)))
    print(f"n={n} m={m} r={r}: {nprime} odd primes in [{lo},{hi}], |Sigma|_C={len(C_em_vecs)}, "
          f"total spurious configs seen={sp_total}, "
          + ("CONTAINMENT HOLDS (e_m subset of sumset) at every prime" if not bad_primes
             else f"VIOLATIONS: {bad_primes[:3]}"))

test(16,2,4, 17, 12000)     # spurious appear here
test(32,2,3, 97, 4000)      # spurious appear here
test(16,2,3, 17, 12000)
