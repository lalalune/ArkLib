# Does max-bad-prime depend on config SIZE (r)? Test n=64, sizes 4 and 6 via MITM.
from itertools import combinations
from sympy import primerange, sqrt_mod
n=64; HALF=32
def spur_size4(p,mu,muset,i2,i3):
    for c2 in combinations(range(n),2):
        if ((c2[0]+HALF)%n)==c2[1]: continue
        us2=[mu[c2[0]],mu[c2[1]]]; S2=sum(us2)%p; T2=sum(pow(u,3,p) for u in us2)%p
        s=(-S2)%p
        if s==0: continue
        P=((pow(s,3,p)+T2)%p)*i3%p*pow(s,p-2,p)%p
        d=(s*s-4*P)%p; r=sqrt_mod(d,p)
        if r is None: continue
        u3=((s+r)*i2)%p; u4=((s-r)*i2)%p
        if u3 not in muset or u4 not in muset: continue
        U=set(c2)|{muset[u3],muset[u4]}
        if len(U)!=4 or any(((j+HALF)%n) in U for j in U): continue
        us=[mu[j] for j in U]
        if sum(us)%p==0 and sum(pow(u,3,p) for u in us)%p==0: return True
    return False
def spur_size6(p,mu,muset,i2,i3):
    for c4 in combinations(range(n),4):
        if any(((j+HALF)%n) in set(c4) for j in c4): continue
        us4=[mu[j] for j in c4]; S4=sum(us4)%p; T4=sum(pow(u,3,p) for u in us4)%p
        s=(-S4)%p
        if s==0: continue
        P=((pow(s,3,p)+T4)%p)*i3%p*pow(s,p-2,p)%p
        d=(s*s-4*P)%p; r=sqrt_mod(d,p)
        if r is None: continue
        u5=((s+r)*i2)%p; u6=((s-r)*i2)%p
        if u5 not in muset or u6 not in muset: continue
        U=set(c4)|{muset[u5],muset[u6]}
        if len(U)!=6 or any(((j+HALF)%n) in U for j in U): continue
        us=[mu[j] for j in U]
        if sum(us)%p==0 and sum(pow(u,3,p) for u in us)%p==0: return True
    return False
bad4=[]; bad6=[]
for p in primerange(129,3000):
    if p%n!=1: continue
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: continue
    mu=[pow(g,j,p) for j in range(n)]; muset={mu[j]:j for j in range(n)}
    i2=pow(2,p-2,p); i3=pow(3,p-2,p)
    if spur_size4(p,mu,muset,i2,i3): bad4.append(p)
    if spur_size6(p,mu,muset,i2,i3): bad6.append(p)
print(f"n=64: size-4 bad primes(<3000)={bad4} max={max(bad4) if bad4 else None}")
print(f"n=64: size-6 bad primes(<3000)={bad6} max={max(bad6) if bad6 else None}")
print(f"=> max-bad-prime size-dependent? size4 max vs size6 max: {max(bad4) if bad4 else 0} vs {max(bad6) if bad6 else 0}")
