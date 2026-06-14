import numpy as np, math
# Decisive test of the bulk/tower split: in the PRIZE regime (p~n^4, structured large-2-part prime),
# (1) do the high moments Sum_periods eta^{2r} explode over the Gaussian/Wick baseline m*(2r-1)!!*n^r ?
# (2) if so, is the explosion confined to IMPRIMITIVE directions (b whose index shares a factor with m's
#     2-power-aligned structure), leaving PRIMITIVE directions sub-Gaussian (ratio ~1)?
# primitive bulk sub-Gaussian + explosion imprimitive  => the split localizes the open problem to the tower.
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
def analyze(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p)
    mu=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    m=(p-1)//n
    eta=np.empty(m); reps=np.empty(m,dtype=np.int64)
    CH=200000
    for s in range(0,m,CH):
        idx=np.arange(s,min(s+CH,m))
        rep=np.array([pow(g,int(i),p) for i in idx],dtype=np.int64)
        prod=(rep[:,None]*mu[None,:])%p
        eta[s:s+len(idx)]=np.cos(2*math.pi*prod/p).sum(axis=1)
    Var=(eta**2).sum()/m
    # primitive = index i with gcd(i,m)==1 ; imprimitive = the rest (includes the 2-power-aligned heavies)
    idxs=np.arange(m)
    from math import gcd
    prim_mask=np.array([gcd(int(i),m)==1 for i in idxs])
    out={'m':m,'Var':Var,'n_prim':int(prim_mask.sum()),'n_imp':int((~prim_mask).sum())}
    for r in [2,3,4,6,8]:
        wick=(np.prod([2*j-1 for j in range(1,r+1)]))*(Var**r)  # (2r-1)!! Var^r per term
        all_ratio=(eta**(2*r)).mean()/wick
        prim_ratio=(eta[prim_mask]**(2*r)).mean()/wick if prim_mask.any() else float('nan')
        imp_ratio=(eta[~prim_mask]**(2*r)).mean()/wick if (~prim_mask).any() else float('nan')
        out[r]=(all_ratio,prim_ratio,imp_ratio)
    return out
print("IN-REGIME moment-explosion split (p~n^4 structured). ratio=E[eta^{2r}]/((2r-1)!!Var^r); ~1=Gaussian.",flush=True)
for n in [32,64]:
    lo=n**4; mu2=int(round(math.log2(n))); step=1<<mu2
    p=(lo//step)*step+1; cnt=0
    while cnt<2 and p<n**5:
        p+=step
        if (p-1)%n: continue
        if v2(p-1)<mu2: continue
        if not isprime(p): continue
        o=analyze(p,n)
        print(f"\np={p} n={n} m={o['m']} Var={o['Var']:.2f} #prim={o['n_prim']} #imprim={o['n_imp']}  logm={math.log(o['m']):.1f}",flush=True)
        print(f"  {'r':>3} {'ALL':>9} {'PRIMITIVE':>10} {'IMPRIMIT':>10}",flush=True)
        for r in [2,3,4,6,8]:
            a,pr,im=o[r]
            print(f"  {r:>3} {a:>9.2f} {pr:>10.2f} {im:>10.2f}",flush=True)
        cnt+=1
print("\nIf PRIMITIVE ratio ~1 (Gaussian) while IMPRIMIT >>1 => explosion is imprimitive-supported, split VALID.",flush=True)
print("If ALL ~1 => no in-regime explosion (residue purely asymptotic). If PRIMITIVE also >>1 => split FALSE.",flush=True)
print("DONE")
