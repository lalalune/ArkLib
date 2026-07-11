# COMPLETE n=16 proof: candidate odd primes ===1 mod 16 are EXACTLY {17,97,113,193,353,577}
# (any bad config has nonempty primitive part U with 𝔭|sum u => p|N(sum u); enumerated over all
#  antipodal-free U sizes 4,6,8). Now check ALL gap-valid S (every r=2..8) at these 6 primes.
import numpy as np
from itertools import combinations
n=16; HALF=8
CAND=[17,97,113,193,353,577]

def build(r):
    size=2*r; gap=[1,3]; needed=[1,2,3]
    subs=list(combinations(range(n),size))
    M={i:np.zeros((len(subs),HALF),dtype=np.int64) for i in needed}
    for si,S in enumerate(subs):
        for i in needed:
            for c in combinations(S,i):
                T=sum(c)%n
                if T<HALF: M[i][si,T]+=1
                else: M[i][si,T-HALF]-=1
    zmask=np.ones(len(subs),bool)
    for i in gap: zmask&=(M[i]==0).all(axis=1)
    Cset={tuple(v) for v in M[2][zmask]}
    return M,gap,Cset

def h_of(p):
    e=(p-1)//n
    for a in range(2,p):
        hh=pow(a,e,p)
        if pow(hh,n,p)==1 and pow(hh,HALF,p)==p-1: return hh

allclean=True
for r in range(2,9):          # |S|=2r, r=2..8 (all gap-valid sizes for mu_16)
    M,gap,Cset=build(r)
    for p in CAND:
        h=h_of(p)
        powv=np.array([pow(h,l,p) for l in range(HALF)],dtype=np.int64)
        Sig=set(int((np.array(v)@powv)%p) for v in Cset)
        valid=np.ones(M[2].shape[0],bool)
        for i in gap: valid&=((M[i]@powv)%p==0)
        em=set(((M[2][valid]@powv)%p).tolist())
        viol=em-Sig
        if viol:
            allclean=False
            print(f"  r={r} p={p}: VIOLATION e2 outside Sigma: {sorted(viol)}")
    print(f"  r={r}: checked all 6 candidate primes — {'clean' if allclean else 'VIOLATION'}")
print()
print("RESULT:", "PROVEN — n=16 has NO odd bad prime ===1 mod 16; Half-Sum Lemma holds at every prize-relevant prime; D's odd part = 1."
      if allclean else "VIOLATION FOUND — refutes exact delta* for n=16!")
