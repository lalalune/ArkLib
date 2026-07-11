# n=128 NEW data point: do spurious configs (antipodal-free, sum u=sum u^3=0) exist, at which primes?
# size-4 MITM (fix 2, solve 2) — exhaustive for size 4.
from itertools import combinations
from sympy import primerange, sqrt_mod
n=128; HALF=64
def spurious4_at(p):
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    i2=pow(2,p-2,p); i3=pow(3,p-2,p)
    mu=[pow(g,j,p) for j in range(n)]
    muset={mu[j]:j for j in range(n)}
    cnt=0
    for c2 in combinations(range(n),2):
        if ((c2[0]+HALF)%n)==c2[1]: continue
        us2=[mu[c2[0]],mu[c2[1]]]
        S2=sum(us2)%p; T2=sum(pow(u,3,p) for u in us2)%p
        s=(-S2)%p
        if s==0: continue
        P=((pow(s,3,p)+T2)%p)*i3%p*pow(s,p-2,p)%p
        disc=(s*s-4*P)%p
        r=sqrt_mod(disc,p)
        if r is None: continue
        u3=((s+r)*i2)%p; u4=((s-r)*i2)%p
        if u3 not in muset or u4 not in muset: continue
        U=set(c2)|{muset[u3],muset[u4]}
        if len(U)!=4 or any(((j+HALF)%n) in U for j in U): continue
        us=[mu[j] for j in U]
        if sum(us)%p==0 and sum(pow(u,3,p) for u in us)%p==0: cnt+=1
    return cnt
prs=[p for p in primerange(129,6000) if p%128==1]
print("n=128 smallest primes ===1 mod 128:", prs[:10])
bad=[]
for p in prs:
    c=spurious4_at(p)
    if c: bad.append((p,c))
    print(f"  p={p} (index {(p-1)//n}): size-4 spurious={c}",flush=True)
print("n=128 size-4 BAD primes <6000:", bad)
