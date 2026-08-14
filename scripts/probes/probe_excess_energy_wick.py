import numpy as np
from math import gcd

def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def factorial2(k):
    r=1
    for j in range(1,2*k,2): r*=j
    return r

def subgroup(p, n):
    e=(p-1)//n
    for cand in range(2,p):
        h=pow(cand,e,p)
        if h==1: continue
        if pow(h, n//2, p)==1: continue
        S=set(); x=1
        for _ in range(n):
            x=(x*h)%p; S.add(x)
        if len(S)==n: return sorted(S)
    raise RuntimeError("no subgroup")

def excess_profile(p, n, rmax=5):
    S=np.array(subgroup(p,n))
    b=np.arange(p)
    eta=np.zeros(p, dtype=complex)
    ang=2j*np.pi/p
    for x in S:
        eta += np.exp(ang*((b*x)%p))
    mag2=np.abs(eta)**2
    M=np.sqrt(mag2[1:].max())
    out={}
    for r in range(1,rmax+1):
        Sr=(mag2[1:]**r).sum()
        out[r]=(Sr/p, factorial2(r)*n**r, (Sr/p)/(factorial2(r)*n**r))
    return M,out

def find_prime(n, target_index):
    for m in range(target_index, target_index*8):
        p=n*m+1
        if isprime(p): return p,m
    return None,None

print("=== EXCESS ENERGY (1/p)sum_{b!=0}|eta_b|^{2r}  vs WICK (2r-1)!! n^r ===")
print("ratio>>1 => energy exceeds Gaussian value => moment route degraded\n")
for n in [8,16,32,64,128]:
    for tgt in [4,16,64,256,1024]:
        p,m=find_prime(n,tgt)
        if p is None or p>500000: continue
        M,prof=excess_profile(p,n)
        ratios=" ".join(f"r{r}:{prof[r][2]:.2f}" for r in prof)
        print(f"n={n:3d} p={p:7d} idx={m:5d} M/√n={M/np.sqrt(n):.2f} M/√p={M/np.sqrt(p):.4f} | {ratios}")
    print()
