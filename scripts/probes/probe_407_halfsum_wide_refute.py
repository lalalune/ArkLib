# Decisive: does ANY prime ===1 mod 16 (prize-relevant) make a gap-valid config have e_2 OUTSIDE Sigma?
# If yes at any p -> exact delta* REFUTED.  Wide range, all gap-valid configs, exact e_2 via Z[zeta].
import numpy as np
from itertools import combinations
from sympy import primerange

def build(n,r):
    HALF=n//2; size=2*r; gap=[1,3]; needed=[1,2,3]
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
    sumvecs=M[2][zmask]
    Cset={tuple(v) for v in sumvecs}
    return M,gap,HALF,Cset,len(Cset)

def hunt(n,r,hi):
    M,gap,HALF,Cset,Ccount=build(n,r)
    viol=[]; mx=0; nump=0
    for p in primerange(17,hi):
        if p%n!=1: continue
        e=(p-1)//n; g=None
        for a in range(2,p):
            gg=pow(a,e,p)
            if pow(gg,n,p)==1 and pow(gg,n//2,p)==p-1: g=gg;break
        if g is None: continue
        nump+=1
        powv=np.array([pow(g,l,p) for l in range(HALF)],dtype=np.int64)
        Sig=set(int((np.array(v)@powv)%p) for v in Cset)
        valid=np.ones(M[2].shape[0],bool)
        for i in gap: valid&=((M[i]@powv)%p==0)
        em=set(((M[2][valid]@powv)%p).tolist())
        if len(em)>mx: mx=len(em)
        if not em<=Sig:
            viol.append((p,sorted(em-Sig)))
            if len(viol)>=2: break
    print(f"n={n} r={r}: |Sigma|={Ccount}; primes(=1 mod {n}) tested={nump} up to {hi}; "
          f"max distinct e_2={mx}; "+("VIOLATIONS "+str(viol)+"  <<< REFUTES" if viol else "NO violation -> Half-Sum holds"))

import sys
hunt(16,3,300000)
hunt(16,4,120000)
hunt(16,5,60000)
