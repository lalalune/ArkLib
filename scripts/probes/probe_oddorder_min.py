import numpy as np, itertools, random
def pfac(n):
    s=set();d=2
    while d*d<=n:
        while n%d==0:s.add(d);n//=d
        d+=1
    if n>1:s.add(n)
    return s
def subgroup(p,n):
    e=(p-1)//n;pf=pfac(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=set();x=1
        for _ in range(n):x=(x*h)%p;S.add(x)
        if len(S)==n:return sorted(S)
    return None
def Cmat(p,S,k):
    Cs=np.array(list(itertools.product(range(p),repeat=k)),dtype=np.int32)
    Xp=np.array([[pow(x,j,p) for j in range(k)] for x in S],dtype=np.int32)
    return (Cs@Xp.T)%p
def worst(p,S,k,r,W=15000,seed=1):
    n=len(S); C=Cmat(p,S,k); rng=np.random.default_rng(seed)
    rand=rng.integers(0,p,size=(W,n)).astype(np.int32)
    idx=rng.integers(0,len(C),size=(W,2)); m=(rng.random((W,n))<0.5)
    mer=np.where(m,C[idx[:,0]],C[idx[:,1]]).astype(np.int32)
    Wds=np.unique(np.concatenate([C,rand,mer],axis=0),axis=0)
    best=0
    for i in range(0,len(Wds),300):
        wd=Wds[i:i+300]
        d=(wd[:,None,:]!=C[None,:,:]).sum(axis=2)
        best=max(best,int((d<=r).sum(axis=1).max()))
    return best
from math import sqrt
print("mu_n worst-case list one past Johnson: EVEN(prize) vs ODD(no -1) vs random",flush=True)
for (n,k,p) in [(8,2,17),(9,2,19),(16,2,17),(8,3,17),(9,3,19),(15,2,31),(16,3,17)]:
    if (p-1)%n: continue
    S=subgroup(p,n)
    if S is None: print(f"n={n} p={p} no subgroup",flush=True); continue
    rho=k/n; r=min(int((1-sqrt(rho))*n)+1, int((1-rho)*n))
    wl=worst(p,S,k,r)
    rs=[worst(p,sorted(random.Random(z+5).sample(range(1,p),n)),k,r,seed=z+9) for z in range(5)]
    Sset=set(S); nc=all((p-x)%p in Sset for x in S)
    v="GENERIC<rand ESCAPE" if wl<min(rs) else ("=rand" if wl<=max(rs) else "WORSE")
    print(f"n={n:3d}({'EVN' if n%2==0 else 'ODD'}) k={k} p={p} negCl={nc} r={r} | mu={wl} rand[{min(rs)}..{max(rs)}] => {v}",flush=True)
