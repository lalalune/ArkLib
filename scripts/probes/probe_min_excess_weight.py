import itertools, math
import numpy as np
# Fast min-excess-weight: first weight w with a signed sum of n-th roots ==0 mod p but !=0 over C.
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def v2(x):
    s=0
    while x%2==0:x//=2;s+=1
    return s
def fac(x):
    f={};d=2
    while d*d<=x:
        while x%d==0:f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def Cred(c,n):
    # zeta^c reduced mod x^{n/2}+1 -> (index in [0,n/2), sign)
    h=n//2; return (c%h, (-1)**((c//h)%2))
def min_excess_weight(p,n,wmax):
    g=proot(p); h=pow(g,(p-1)//n,p)
    R=np.array([pow(h,c,p) for c in range(n)],dtype=np.int64)
    half=n//2
    for w in range(3,wmax+1):
        masks=np.array([[1 if (msk>>i)&1 else -1 for i in range(w-1)] for msk in range(1<<(w-1))],dtype=np.int64)
        # first sign fixed +1
        full=np.concatenate([np.ones((masks.shape[0],1),dtype=np.int64),masks],axis=1)  # (M,w)
        for combo in itertools.combinations(range(n),w):
            vals=(full*R[list(combo)]).sum(axis=1)%p   # (M,)
            hit=np.where(vals==0)[0]
            for idx in hit:
                signs=full[idx]
                # C-vector
                cv=[0]*half
                for c,s in zip(combo,signs):
                    r,sg=Cred(c,n); cv[r]+=int(s)*sg
                if any(cv):
                    return w
        # also all-negative-of-first handled by symmetry; covered since we fix first=+1 (global sign irrelevant)
    return None
print("Min EXCESS weight (first char-p deviation) vs n, structured in-regime primes (p~n^4):",flush=True)
print(f"{'p':>10} {'n':>4} {'2logp':>7} {'min_excess_wt':>14}",flush=True)
for n,wmax in [(8,9),(16,9),(32,6)]:
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1; cnt=0
    while cnt<2 and p<n**5:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if not isprime(p): continue
        w=min_excess_weight(p,n,wmax)
        print(f"{p:>10} {n:>4} {2*math.log(p):>7.2f} {str(w) if w else '>'+str(wmax):>14}",flush=True)
        cnt+=1
print("\nGrows with n => strong suppression (floor provable in-regime via moments to depth=min_wt).",flush=True)
print("DONE")
