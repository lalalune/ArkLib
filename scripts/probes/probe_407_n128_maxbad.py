# Test growth law "max bad prime < Q^2" at n=128 (Q^2=16384). Size-6 MITM (exhaustive for size 6).
from itertools import combinations
from sympy import primerange, sqrt_mod
n=128; HALF=64
def spurious6_at(p):
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    i2=pow(2,p-2,p); i3=pow(3,p-2,p)
    mu=[pow(g,j,p) for j in range(n)]; muset={mu[j]:j for j in range(n)}
    for c4 in combinations(range(n),4):
        if any(((j+HALF)%n) in set(c4) for j in c4): continue
        us4=[mu[j] for j in c4]
        S4=sum(us4)%p; T4=sum(pow(u,3,p) for u in us4)%p
        s=(-S4)%p
        if s==0: continue
        P=((pow(s,3,p)+T4)%p)*i3%p*pow(s,p-2,p)%p
        disc=(s*s-4*P)%p
        r=sqrt_mod(disc,p)
        if r is None: continue
        u5=((s+r)*i2)%p; u6=((s-r)*i2)%p
        if u5 not in muset or u6 not in muset: continue
        U=set(c4)|{muset[u5],muset[u6]}
        if len(U)!=6 or any(((j+HALF)%n) in U for j in U): continue
        us=[mu[j] for j in U]
        if sum(us)%p==0 and sum(pow(u,3,p) for u in us)%p==0: return True
    return False
prs=[p for p in primerange(129,16500) if p%128==1]
bad=[]
for p in prs:
    if spurious6_at(p): bad.append(p)
print(f"n=128 (Q^2=16384): #primes scanned={len(prs)} (to 16500); size-6 BAD primes={bad}")
print(f"  max bad={max(bad) if bad else None}; all < Q^2=16384? {all(b<16384 for b in bad)}")
