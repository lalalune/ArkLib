import itertools, math
import numpy as np
from sympy import primitive_root, isprime

def roots(n,p,g): return [pow(g,j,p) for j in range(n)]

def count_e2_n32(n, p):
    """w=n/2. Split mu into two halves of size n/2. Enumerate kL from L (0..n/2),
       kR=w-kL from R. Use numpy to vectorize the (s1L,s2L) x (s1R,s2R) match."""
    g = pow(primitive_root(p), (p-1)//n, p)
    mu = roots(n,p,g)
    half=n//2; w=half
    L=list(range(half)); R=list(range(half,n))
    muL=[mu[i] for i in L]; muR=[mu[i] for i in R]
    e1set=set(); cnt=0
    for kL in range(0, w+1):
        kR=w-kL
        if kR<0 or kR>len(R): continue
        # L combos
        Ls1=[]; Ls2=[]
        for c in itertools.combinations(range(half), kL):
            s1=0;s2=0
            for i in c: s1+=muL[i]; s2+=muL[i]*muL[i]
            Ls1.append(s1%p); Ls2.append(s2%p)
        Rs1=[]; Rs2=[]
        for c in itertools.combinations(range(half), kR):
            s1=0;s2=0
            for i in c: s1+=muR[i]; s2+=muR[i]*muR[i]
            Rs1.append(s1%p); Rs2.append(s2%p)
        Ls1=np.array(Ls1,dtype=np.int64); Ls2=np.array(Ls2,dtype=np.int64)
        Rs1=np.array(Rs1,dtype=np.int64); Rs2=np.array(Rs2,dtype=np.int64)
        # for each L, need R such that (s1L+s1R)^2 = s2L+s2R mod p, s1L+s1R != 0
        # iterate over L (smaller side typically); vectorize over R
        for i in range(len(Ls1)):
            s1L=int(Ls1[i]); s2L=int(Ls2[i])
            s1=(s1L+Rs1)%p
            s2=(s2L+Rs2)%p
            lhs=(s1*s1 - s2)%p
            mask=(lhs==0)&(s1!=0)
            good=s1[mask]
            cnt+=len(good)
            for v in good.tolist(): e1set.add(int(v))
    rem=set(e1set); K=0
    while rem:
        x=next(iter(rem)); rem -= set((u*x)%p for u in mu); K+=1
    return cnt, len(e1set), K

n=32; p=n**4
while not ((p-1)%n==0 and isprime(p)): p+=1
print(f"n=32 w=16 p={p} (beta=4)...")
cnt,dist,K=count_e2_n32(n,p)
print(f"  #bad-sets={cnt}  #distinct-e1={dist}  K(orbits)={K}  K/n={K/n:.3f}  dist/n={dist/n:.2f}")
