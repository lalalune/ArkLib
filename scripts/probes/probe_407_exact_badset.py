# Exact bad-prime set: which p===1 mod n have ANY spurious (antipodal-free, sum u=sum u^3=0) config?
# Check ALL sizes, scan wide. Determine if bad set is small/characterizable.
from itertools import combinations
from sympy import primerange
def spurious_exists(n,p,sizes):
    HALF=n//2
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return None
    mu=[pow(g,j,p) for j in range(n)]
    total=0
    for size in sizes:
        for S in combinations(range(n),size):
            if any(((j+HALF)%n) in set(S) for j in S): continue
            us=[mu[j] for j in S]
            if sum(us)%p!=0: continue
            if sum(pow(u,3,p) for u in us)%p!=0: continue
            total+=1
    return total

for (n,sizes,hi) in [(16,[4,6,8],8000),(32,[4,6],3000)]:
    bad=[]
    for p in primerange(n+1,hi):
        if p%n!=1: continue
        t=spurious_exists(n,p,sizes)
        if t and t>0: bad.append((p,t))
    smallest=[p for p in primerange(n+1,hi) if p%n==1][:5]
    print(f"n={n} sizes={sizes} (scan<{hi}): smallest primes={smallest}; BAD primes (with #spurious) = {bad}")
