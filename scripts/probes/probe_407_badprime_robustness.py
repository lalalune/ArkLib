# Robustness of (star): is MAX bad prime < N0 across all r? And no LARGE bad prime for n=16?
from itertools import combinations
from sympy import primerange
def N0(n,r):
    HALF=n//2; vecs=set()
    for W in combinations(range(HALF),r):
        v=[0]*HALF
        for l in W:
            e=(2*l)%n
            if e<HALF: v[e]+=1
            else: v[e-HALF]-=1
        vecs.add(tuple(v))
    return len(vecs)
def has_spurious(n,p,sizes):
    HALF=n//2; e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return False
    mu=[pow(g,j,p) for j in range(n)]
    for size in sizes:
        for S in combinations(range(n),size):
            if any(((j+HALF)%n) in set(S) for j in S): continue
            us=[mu[j] for j in S]
            if sum(us)%p!=0: continue
            if sum(pow(u,3,p) for u in us)%p!=0: continue
            return True
    return False

# n=16: scan ALL primes ===1 mod 16 up to 50000 (sizes 4,6,8) -> is bad set really just {17}?
print("=== n=16: ALL bad primes up to 50000 (sizes 4,6,8) ===")
N0_16 = {r: N0(16,r) for r in [2,3,4]}
print("N0(16,r):", N0_16)
bad16=[]
for p in primerange(17, 50000):
    if p%16!=1: continue
    if has_spurious(16,p,[4,6,8]): bad16.append(p)
print("bad primes n=16 (<50000):", bad16, " => max bad =", max(bad16) if bad16 else None, "; N0 range", min(N0_16.values()),"-",max(N0_16.values()))
