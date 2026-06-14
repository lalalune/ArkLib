import numpy as np, itertools, random
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
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
def worst_list(p,S,k,r,W=40000,seed=1):
    n=len(S)
    Cs=np.array(list(itertools.product(range(p),repeat=k)),dtype=np.int64)  # (p^k,k)
    Xp=np.array([[pow(x,j,p) for j in range(k)] for x in S],dtype=np.int64)  # (n,k)
    C=(Cs@Xp.T)%p   # (p^k, n) codewords
    rng=np.random.default_rng(seed)
    # candidate words: random + each codeword + pairwise merges
    rand=rng.integers(0,p,size=(W,n))
    merges=[]
    idx=rng.integers(0,len(C),size=(W,2)); m=(rng.random((W,n))<0.5)
    merges=np.where(m, C[idx[:,0]], C[idx[:,1]])
    Wds=np.concatenate([C, rand, merges],axis=0)
    Wds=np.unique(Wds,axis=0)
    best=0
    # chunk over codewords to bound memory
    for i in range(0,len(Wds),2000):
        wd=Wds[i:i+2000]  # (b,n)
        # distance to each codeword: (b, p^k)
        d=(wd[:,None,:]!=C[None,:,:]).sum(axis=2)
        cnt=(d<=r).sum(axis=1)
        best=max(best,int(cnt.max()))
    return best
from math import sqrt
print("Even mu_n (neg-closed, PRIZE) vs ODD mu_n (-1 NOT in mu_n) vs random, worst-case list one past Johnson.")
print("odd-order < random => GENERIC => negation symmetry WAS the obstruction => escape.\n")
for (n,k,p) in [(8,2,17),(9,2,19),(16,2,17),(25,2,101),(27,2,109),(8,3,17),(9,3,19)]:
    if (p-1)%n: 
        print(f"n={n} p={p}: n nmid p-1"); continue
    S=subgroup(p,n)
    if S is None: print(f"n={n} p={p}: no subgroup"); continue
    rho=k/n; r=int((1-sqrt(rho))*n)+1; r=min(r,int((1-rho)*n))
    wl=worst_list(p,S,k,r)
    rs=[worst_list(p,sorted(random.Random(z+5).sample(range(1,p),n)),k,r,seed=z+9) for z in range(5)]
    Sset=set(S); nc=all((p-x)%p in Sset for x in S)
    v="GENERIC < rand  *** ESCAPE ***" if wl<min(rs) else ("= random (no escape)" if wl<=max(rs) else "WORSE than random")
    print(f"n={n:3d}({'EVEN' if n%2==0 else 'ODD '}) k={k} p={p:4d} negClosed={nc} r={r} d={r/n:.2f} | mu_n={wl}  random[{min(rs)}..{max(rs)}]  => {v}")
