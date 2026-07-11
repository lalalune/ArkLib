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
def maxtwist(p, roots, d, c):
    # max_b | sum_{x in roots} e_p(b x + c x^d) |
    rr=np.array(roots,dtype=np.int64)
    xd=(np.array([pow(int(x),d,p) for x in rr],dtype=np.int64)*c)%p   # c*x^d
    base=np.exp(2j*np.pi*xd/p)   # the twist phase per root (b-independent)
    M=0.0; BL=8000
    for i in range(1,p,BL):
        bb=np.arange(i,min(i+BL,p),dtype=np.int64)[:,None]
        ph=(np.exp(2j*np.pi*((bb*rr[None,:])%p)/p)*base[None,:]).sum(axis=1)
        M=max(M,float(np.abs(ph).max()))
    return M

print("WILD-TWIST test: max_b |Σ_{x∈μ_n} e_p(bx + c·x^d)| vs M (d=1,c=0). Does poly-phase twist reduce M?")
print("(On F_p the 'wild ASW' twist = e_p(poly(x)); d=2 quadratic/metaplectic, d=3 cubic)")
print("="*72)
for n,p in [(16,65537),(32,1048609)]:
    roots=subgroup(p,n)
    M0=maxtwist(p,roots,1,0)   # untwisted = M
    print(f"\nn={n} p={p}: M (untwisted) = {M0:.3f}  (M/√n={M0/sqrt(n):.3f}, M/√(n log p)={M0/sqrt(n*log(p)):.3f})")
    for d in (2,3):
        vals=[maxtwist(p,roots,d,c) for c in (1,2,7)]
        print(f"  d={d} (degree-{d} twist) max over c∈{{1,2,7}}: {[f'{v:.2f}' for v in vals]}  "
              f"min/√n={min(vals)/sqrt(n):.3f}  vs M/√n={M0/sqrt(n):.3f}  "
              f"{'SMALLER (twist helps the twisted sum)' if min(vals)<M0 else 'NOT smaller'}")
print()
print("VERDICT: the twisted sum is a DIFFERENT object (eta^W != eta_b = M). Even if max|eta^W| is")
print("smaller/Ramanujan, it does NOT bound M (no transfer: M = max over UNtwisted b). The wild twist")
print("on F_p = a poly-phase sum, a different incomplete exponential sum with its OWN Burgess problem.")
