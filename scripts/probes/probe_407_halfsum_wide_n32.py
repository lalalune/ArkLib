# Wide refutation hunt n=32: does any prime ===1 mod 32 inflate #bad above |Sigma|? (r=3)
import numpy as np
from itertools import combinations
from sympy import primerange
n=32; HALF=16; r=3; size=2*r; gap=[1,3]; needed=[1,2,3]
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
Cset={tuple(v) for v in M[2][zmask]}; Ccount=len(Cset)
print(f"n=32 r=3: |Sigma|={Ccount}, #configs={len(subs)}",flush=True)
viol=[]; mx=0; nump=0
for p in primerange(33, 60000):
    if p%n!=1: continue
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: continue
    nump+=1
    powv=np.array([pow(g,l,p) for l in range(HALF)],dtype=np.int64)
    Sig=set(int((np.array(v)@powv)%p) for v in Cset)
    valid=np.ones(len(subs),bool)
    for i in gap: valid&=((M[i]@powv)%p==0)
    em=set(((M[2][valid]@powv)%p).tolist())
    if len(em)>mx: mx=len(em)
    if not em<=Sig:
        viol.append((p,sorted(em-Sig)))
        if len(viol)>=2: break
print(f"n=32 r=3: primes tested={nump} up to 60000; max distinct e2={mx} (|Sigma|={Ccount}); "
      + (f"VIOLATIONS {viol} <<< REFUTES" if viol else "NO violation -> holds"),flush=True)
