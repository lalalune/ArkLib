import itertools, random
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def find_p(n, lo=20):
    for m in range(lo, lo*40):
        p=n*m+1
        if isprime(p): return p
    return None
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        ok=all(pow(h,n//q,p)!=1 for q in set([d for d in range(2,n+1) if n%d==0 and isprime(d)]))
        if not ok: continue
        S=[];x=1
        for _ in range(n): x=(x*h)%p; S.append(x)
        if len(set(S))==n: return sorted(set(S))
    return None
def codewords(p,S,k):
    n=len(S)
    return [tuple(sum(c[j]*pow(x,j,p) for j in range(k))%p for x in S) for c in itertools.product(range(p),repeat=k)]
def worst_list(p,S,k,r,nsamp):
    n=len(S); C=codewords(p,S,k); rng=random.Random(7)
    best=0
    cands=list(C)
    for _ in range(nsamp): cands.append(tuple(rng.randrange(p) for _ in range(n)))
    # structured: agree with c1 on a subset, c2 elsewhere
    for _ in range(nsamp//2):
        c1=rng.choice(C);c2=rng.choice(C)
        mask=[rng.random()<0.5 for _ in range(n)]
        cands.append(tuple(c1[i] if mask[i] else c2[i] for i in range(n)))
    seen=set()
    for w in cands:
        if w in seen: continue
        seen.add(w)
        cnt=sum(1 for c in C if sum(1 for i in range(n) if c[i]!=w[i])<=r)
        if cnt>best: best=cnt
    return best
def negclosed(p,S):
    Ss=set(S); return all((p-x)%p in Ss for x in S)
from math import sqrt
print("Worst-case list: even-order mu_n (neg-closed, prize) vs ODD-order mu_n (NOT neg-closed) vs random.")
print("If odd-order < random => GENERIC => floor holds there (escapes negation refutation).\n")
cases=[(8,2),(9,2),(16,2),(25,2),(27,2)]
for (n,k) in cases:
    p=find_p(n)
    if p is None: continue
    S=subgroup(p,n)
    if S is None: continue
    rho=k/n; Jr=int((1-sqrt(rho))*n); capr=int((1-rho)*n)
    r=min(Jr+1, capr)  # one past Johnson
    nsamp=4000 if p**k>3000 else 30000
    wl_mu=worst_list(p,S,k,r,nsamp)
    rng=random.Random(99); rsubs=[]
    for _ in range(6):
        T=sorted(random.Random(_+1).sample(range(1,p),n)); rsubs.append(worst_list(p,T,k,r,nsamp))
    parity="EVEN(neg-closed)" if n%2==0 else "ODD(NOT neg-closed)"
    nc=negclosed(p,S)
    rmin,rmax=min(rsubs),max(rsubs)
    verdict="GENERIC(<random) ESCAPE!" if wl_mu<rmin else ("=random" if rmin<=wl_mu<=rmax else "WORSE than random")
    print(f"n={n:3d}({parity[:4]}) k={k} p={p:6d} negClosed={nc} | r={r} delta={r/n:.2f} | mu_n list={wl_mu}  random[{rmin}..{rmax}]  => {verdict}")
