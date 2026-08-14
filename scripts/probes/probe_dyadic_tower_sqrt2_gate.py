import numpy as np
from math import sqrt, log2

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
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
def v2(x):
    k=0
    while x%2==0:x//=2;k+=1
    return k
def M_of(p, roots):
    # M = max_{b!=0} |sum_{x in roots} e_p(b x)|
    g=primroot(p)  # not needed
    M=0.0; BL=4000
    rr=np.array(roots)
    for i in range(1,p,BL):
        bb=np.arange(i,min(i+BL,p))[:,None]
        ph=np.exp(2j*np.pi*((bb*rr[None,:])%p)/p).sum(axis=1)
        M=max(M,np.abs(ph).max())
    return M
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S

# pick generic primes with high v2(p-1), moderate size
print("DYADIC TOWER: M(mu_{2^k})/M(mu_{2^{k-1}}) — √2≈1.414 (cancel→prize √n) vs 2 (no cancel→trivial n)")
print("="*74)
for p in (12289, 40961, 786433):   # 12289=2^12*3+1, 40961=2^13*5+1, 786433=2^18*3+1 (check)
    if not is_prime(p): continue
    V=v2(p-1); Kmax=min(V, 13)
    Ms=[]
    for k in range(1,Kmax+1):
        n=2**k
        Ms.append(M_of(p, subgroup(p,n)))
    print(f"\np={p} (v2(p-1)={V}); M(mu_n) and ratio + M/sqrt(n):")
    for k in range(1,Kmax+1):
        n=2**k; rat = Ms[k-1]/Ms[k-2] if k>=2 else float('nan')
        print(f"  k={k:2d} n={n:5d}: M={Ms[k-1]:8.2f}  ratio={rat:.3f}  M/sqrt(n)={Ms[k-1]/sqrt(n):.3f}")
    # does the ratio approach sqrt2 (prize) or 2 (trivial)? base vs deep
    deep_ratios=[Ms[k-1]/Ms[k-2] for k in range(max(2,Kmax-4),Kmax+1)]
    print(f"  ==> deep-level ratios (last 4): {[f'{r:.3f}' for r in deep_ratios]}  (→√2={sqrt(2):.3f} prize, →2 trivial)")
