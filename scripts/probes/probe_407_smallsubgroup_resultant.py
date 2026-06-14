from itertools import combinations
from sympy import primerange
def bad_primes(s, sizes, pmax):
    bad=[]
    for p in primerange(s+1, pmax):
        if p%s!=1: continue
        e=(p-1)//s; g=None
        for a in range(2,p):
            gg=pow(a,e,p)
            if pow(gg,s,p)==1 and pow(gg,s//2,p)==p-1: g=gg;break
        if g is None: continue
        mu=[pow(g,j,p) for j in range(s)]
        found=False
        for size in sizes:
            if size>s: continue
            for S in combinations(range(s),size):
                if any(((j+s//2)%s) in set(S) for j in S): continue
                us=[mu[j] for j in S]
                if sum(us)%p!=0: continue
                if sum(pow(u,3,p) for u in us)%p!=0: continue
                found=True; break
            if found: break
        if found: bad.append(p)
    return bad
for (s,sizes,pmax) in [(8,[4,6],300),(16,[4,6,8],20000)]:
    bad=bad_primes(s,sizes,pmax)
    print(f"mu_{s} (2^s={2**s}, scan<{pmax}): bad={bad}; all<2^s? {all(b<2**s for b in bad)}; all<s^3={s**3}? {all(b<s**3 for b in bad)}", flush=True)
