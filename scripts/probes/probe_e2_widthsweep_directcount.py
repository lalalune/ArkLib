import itertools, math
import numpy as np
from sympy import primitive_root, isprime

def roots(n,p,g): return [pow(g,j,p) for j in range(n)]

def count_e2_at_w(n, p, w):
    """count distinct e1 over e2=0,e1!=0 locus at subset-size w. MITM."""
    g = pow(primitive_root(p), (p-1)//n, p)
    mu = roots(n,p,g)
    half=n//2
    muL=mu[:half]; muR=mu[half:]
    e1set=set(); cnt=0
    for kL in range(0, w+1):
        kR=w-kL
        if kR<0 or kR>len(muR) or kL>len(muL): continue
        Ls1=[];Ls2=[]
        for c in itertools.combinations(range(len(muL)),kL):
            s1=sum(muL[i] for i in c)%p; s2=sum((muL[i]**2) for i in c)%p
            Ls1.append(s1);Ls2.append(s2)
        Rs1=[];Rs2=[]
        for c in itertools.combinations(range(len(muR)),kR):
            s1=sum(muR[i] for i in c)%p; s2=sum((muR[i]**2) for i in c)%p
            Rs1.append(s1);Rs2.append(s2)
        Rs1=np.array(Rs1,dtype=np.int64);Rs2=np.array(Rs2,dtype=np.int64)
        for i in range(len(Ls1)):
            s1=(Ls1[i]+Rs1)%p; s2=(Ls2[i]+Rs2)%p
            mask=((s1*s1-s2)%p==0)&(s1!=0)
            for v in s1[mask].tolist(): e1set.add(int(v)); 
            cnt+=int(mask.sum())
    rem=set(e1set);K=0
    while rem:
        x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
    return cnt,len(e1set),K

# For the two-monomial pencil x^k + a x^{k+1}: bad at agreement w means subset size w,
# e2=0 corresponds to b=k+2 i.e. agreement w=k+2.  The RELATIVE agreement is w/n.
# prize window interior: agreement frac in (sqrt(rho), 1 - Theta(1/log n)) roughly,
# i.e. distance delta in (1-sqrt(rho)... ).  Let's just sweep w and report agreement frac.
for n in [16,32]:
    p=n**4
    while not ((p-1)%n==0 and isprime(p)): p+=1
    print(f"=== n={n} p={p} ===  (agreement w, dist=1-w/n)")
    for w in range(3, n//2+2):
        cnt,dist,K=count_e2_at_w(n,p,w)
        if dist>0:
            print(f"  w={w:2d} agree={w/n:.3f} dist={1-w/n:.3f}: #distinct-e1={dist:5d} K={K:3d} (K/n={K/n:.2f})")
