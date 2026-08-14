"""
Measure the structure of E_r(F_p)/Wick -> 0 to ground the conjectures.
Wick=(2r-1)!!*n^r. Compute ratio, log-ratio decay, second differences, and the IMPLIED decay law.
Also: is the ratio's decay c^r (geometric), exp(-ar^2) (Gaussian-tail), or 1/poly?
"""
from collections import Counter
import math
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
def Er(p,n,R):
    c=Counter({0:1}); E={}
    S=subgroup(p,n)
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc; E[r]=sum(m*m for m in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
print("E_r(F_p)/Wick decay structure (Wick=(2r-1)!!*n^r):")
for n,p in [(16,65537),(32,1048609)]:
    E=Er(p,n,min(2*n-2,14))
    print(f" n={n} p={p}:")
    print(f"   {'r':>2} {'ratio':>8} {'log ratio':>9} {'d(log)/dr':>9} {'ratio^(1/r)':>11}")
    prev=None
    for r in range(2,len(E)):
        rt=E[r]/(dfac(r)*n**r)
        lr=math.log(rt)
        dl = (lr-prev) if prev is not None else 0
        print(f"   {r:>2} {rt:>8.4f} {lr:>9.3f} {dl:>9.3f} {rt**(1/r):>11.4f}")
        prev=lr
print()
print("=> if d(log ratio)/dr is roughly CONSTANT (-c) => ratio ~ e^{-cr} GEOMETRIC decay (provable target).")
print("   if it gets MORE negative => super-geometric (faster). The decay LAW informs the conjectures.")
