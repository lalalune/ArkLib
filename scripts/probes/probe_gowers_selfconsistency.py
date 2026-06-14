# Verify NEW identities for the 2^mu subgroup character sum:
#  (I1)  |eta_b|^2 = n + sum_{x in mu_n, x!=1} eta_{b(1-x)}              [self-consistency]
#  (I2)  ||phi_b||_{U^2}^4 = (1/n^2) sum_{h} eta_{b(1-g^h)}             [Gowers U^2]
# and probe whether the secondary sum S(b)=sum_{x in mu_n} eta_{b(1-x)} is O(n) (=> |eta|^2=O(n)).
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def gmu(p,n):
    g=pow(primroot(p),(p-1)//n,p); return g,[pow(g,i,p) for i in range(n)]
def eta(b,roots,p):
    if b%p==0: return complex(len(roots),0)
    s=0j
    for x in roots: s+=cmath.exp(2j*math.pi*(b*x%p)/p)
    return s
for (n,trip) in [(8,None),(16,None),(32,None)]:
    p=n+1
    while not isprime(p): p+=n
    while p<400: p+=n
    while not isprime(p): p+=n
    g,roots=gmu(p,n)
    # test I1 and the secondary-sum size over several b
    maxratio=0; worstS=0; ok1=True
    for b in range(1,p):
        e=eta(b,roots,p)
        # secondary sum over x in mu_n, x!=1
        S=sum(eta((b*(1-x))%p,roots,p) for x in roots if x%p!=1)
        lhs=abs(e)**2; rhs=n+S.real
        if abs(lhs-rhs)>1e-6: ok1=False
        # |S| size vs n
        if abs(S)>worstS: worstS=abs(S)
        r=abs(e)/math.sqrt(n)
        if r>maxratio: maxratio=r
    print(f"n={n} p={p}: I1 |eta|^2=n+S exact? {ok1}.  max|eta|/sqrt(n)={maxratio:.3f}  worst|S|/n={worstS/n:.3f}  worst|S|/(n log n)={worstS/(n*math.log(n)):.3f}",flush=True)
