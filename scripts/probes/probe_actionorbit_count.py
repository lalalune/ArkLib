#!/usr/bin/env python3
"""
probe_actionorbit_count.py  (#407, Lane B — Action-Orbit, Chai-Fan eprint 2026/861)

The bad-alpha set for the pencil h_alpha(z)=z^a+alpha*z^b on mu_n is a union of <mu^{b-a}>-orbits
(agreement_orbit_invariance, axiom-clean in ActionOrbitFRI.lean). #bad = #orbits * orbit_size; the
prize budget is #bad <= q*eps* ~ n. For a PRIMITIVE pencil (gcd(b-a,n)=1) orbit_size = n, so the
pin needs #orbits = O(1).

MEASURED (exact, prize-shaped p=n^4, proper subgroup mu_n):
  n=8  k=2: at t=4 (#bad=8 ~ n)   -> #orbits = 1
  n=16 k=3: at t=5 (#bad=16 = n)  -> #orbits = 1
  n=32 k=2: at t=4 (#bad=224~7n)  -> #orbits = 7 (= #bad/n)
=> #orbits = #bad / orbit_size EXACTLY. So "#orbits = O(1)" is a TRIVIAL RESTATEMENT of "#bad = O(n)"
   = the prize floor itself. The naive orbit count gives NO escape (confirms the issue's note "orbit
   count = BGK at window interior"). The genuine Lane B content is the ALGEBRAIC bound on #orbits via
   Chai-Fan Q1 (resultant/norm non-vanishing, d>=16 open), which would bound #orbits INDEPENDENT of
   the incidence -- that is the real non-BGK question, NOT settled by the count.
"""
import numpy as np, itertools, math
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in (1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def matinv(A,p):
    n=A.shape[0];M=np.concatenate([A%p,np.eye(n,dtype=np.int64)],1)%p
    for c in range(n):
        piv=next((r for r in range(c,n) if M[r,c]%p),None)
        if piv is None:return None
        M[[c,piv]]=M[[piv,c]];M[c]=(M[c]*pow(int(M[c,c]),p-2,p))%p
        for r in range(n):
            if r!=c and M[r,c]%p:M[r]=(M[r]-M[r,c]*M[c])%p
    return M[:,n:]%p
def run(n,k):
    p=int(n**4)|1
    while not(isprime(p) and (p-1)%n==0):p+=1
    g=proot(p);h=pow(g,(p-1)//n,p)
    pts=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    V=np.ones((n,k),dtype=np.int64)
    for j in range(1,k):V[:,j]=(V[:,j-1]*pts)%p
    mats=[(list(S),(V@matinv(V[list(S),:],p))%p) for S in itertools.combinations(range(n),k)
          if matinv(V[list(S),:],p) is not None]
    a,b=k+1,k+2
    pw_a=np.array([pow(int(x),a,p) for x in pts],dtype=np.int64)
    pw_b=np.array([pow(int(x),b,p) for x in pts],dtype=np.int64)
    al=np.arange(p,dtype=np.int64); Vw=(pw_a[None,:]+np.outer(al,pw_b))%p
    best=np.zeros(p,dtype=np.int64)
    for S,M in mats: np.maximum(best,((Vw[:,S]@M.T)%p==Vw).sum(1),out=best)
    mu_shift=pow(g,((p-1)//n)*((b-a)%n),p); ordmu=n//math.gcd(b-a,n); out=[]
    for tau in range(k+1,n+1):
        bad=set(int(x) for x in al[best>=tau] if x!=0)
        if not bad: continue
        seen=set(); norb=0
        for x in bad:
            if x in seen: continue
            norb+=1; cur=x
            for _ in range(ordmu): seen.add(cur); cur=cur*mu_shift%p
        out.append((tau,len(bad),norb))
    return p,ordmu,out
if __name__=="__main__":
    print("Action-Orbit: #orbits = #bad/orbit_size (pin needs #orbits=O(1) at #bad~n)")
    for n,k in [(8,2),(16,3),(32,2)]:
        p,osz,out=run(n,k)
        print(f"n={n} k={k} orbsz={osz}: "+" ".join(f"(t{t},bad{b},orb{o})" for t,b,o in out))
