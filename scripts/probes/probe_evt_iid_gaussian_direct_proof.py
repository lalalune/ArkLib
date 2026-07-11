import numpy as np
from math import sqrt, log
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def M_of(p,roots):
    rr=np.array(roots,dtype=np.int64);M=0.0;BL=8000
    for i in range(1,p,BL):
        bb=np.arange(i,min(i+BL,p),dtype=np.int64)[:,None]
        M=max(M,float(np.abs(np.exp(2j*np.pi*((bb*rr[None,:])%p)/p).sum(axis=1)).max()))
    return M
def find(target,n):
    p=target-(target%n)+1
    for _ in range(2000):
        if (p-1)%n==0 and is_prime(p): return p
        p+=n
    return None
print("DIRECT-PROOF EVT structure: is M ~ the iid-Gaussian extreme value sqrt(2 n log N), N=(p-1)/n?")
print("  C_iid = M / sqrt(2 n log((p-1)/n))  — if ~1 (and <=1), family is sub-iid-Gaussian ⟹ prize C=sqrt2")
print("="*74)
for mu in (4,5,6):
    n=2**mu; p=find(n**4,n)
    if not p: continue
    roots=subgroup(p,n); M=M_of(p,roots)
    N=(p-1)/n
    C_iid = M/sqrt(2*n*log(N))
    C_logp = M/sqrt(n*log(p/n))
    print(f"n={n:3d} p={p:9d}: M={M:7.2f}  N=(p-1)/n={N:.0f}  C_iid=M/sqrt(2n log N)={C_iid:.4f}  "
          f"M/sqrt(n log(p/n))={C_logp:.4f}  (sqrt2={sqrt(2):.3f})")
print()
print("READING: C_iid ~ 1 ⟹ M tracks the iid-Gaussian extreme value exactly; C_iid < 1 ⟹ sub-iid")
print("(negative dependence helps). The DIRECT PROOF = 'family sub-Gaussian to depth log p' ⟹ M<=sqrt(2n log N).")
print("The WALL-STEP = the deep-depth (k~log p) sub-Gaussianity = the char-p archimedean phase.")
