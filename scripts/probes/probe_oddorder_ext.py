import numpy as np, itertools, random
def pfac(n):
    s=set();d=2
    while d*d<=n:
        while n%d==0:s.add(d);n//=d
        d+=1
    if n>1:s.add(n)
    return s
def isprime(n):
    if n<2:return False
    i=2
    while i*i<=n:
        if n%i==0:return False
        i+=1
    return True
def smallp(n):
    for m in range(1,200):
        p=n*m+1
        if isprime(p) and p<=43: return p
    return None
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
def worst(p,S,k,r,W=12000,seed=1):
    n=len(S)
    Cs=np.array(list(itertools.product(range(p),repeat=k)),dtype=np.int32)
    Xp=np.array([[pow(x,j,p) for j in range(k)] for x in S],dtype=np.int32)
    C=(Cs@Xp.T)%p; rng=np.random.default_rng(seed)
    rand=rng.integers(0,p,size=(W,n)).astype(np.int32)
    idx=rng.integers(0,len(C),size=(W,2)); m=(rng.random((W,n))<0.5)
    mer=np.where(m,C[idx[:,0]],C[idx[:,1]]).astype(np.int32)
    Wds=np.unique(np.concatenate([C,rand,mer],axis=0),axis=0)
    best=0
    for i in range(0,len(Wds),250):
        d=(Wds[i:i+250][:,None,:]!=C[None,:,:]).sum(axis=2)
        best=max(best,int((d<=r).sum(axis=1).max()))
    return best
from math import sqrt
print("EVEN vs ODD multiplicative subgroup genericity (worst-case list vs random), k=2, multiple n:",flush=True)
for n in [8,9,10,15,16,21,25,27]:
    p=smallp(n)
    if p is None: print(f"n={n}: no small prime",flush=True); continue
    if p*p>2500: 
        # cap codeword count
        pass
    k=2; rho=k/n
    for r in [int((1-sqrt(rho))*n), int((1-sqrt(rho))*n)+1]:
        if r>=int((1-rho)*n)+1: continue
        S=subgroup(p,n)
        if S is None: print(f"n={n} p={p} no subgroup",flush=True); break
        wl=worst(p,S,k,r)
        rs=[worst(p,sorted(random.Random(z+5).sample(range(1,p),n)),k,r,seed=z+9) for z in range(6)]
        Sset=set(S); nc=all((p-x)%p in Sset for x in S)
        rmean=sum(rs)/len(rs)
        flag="<RAND(GENERIC!)" if wl<min(rs) else (">RAND(worse)" if wl>max(rs) else "~rand")
        print(f"n={n:2d}({'E' if n%2==0 else 'O'}) p={p} negCl={int(nc)} r={r} d={r/n:.2f} | mu={wl} rand{rs} mean={rmean:.1f} => {flag}",flush=True)
