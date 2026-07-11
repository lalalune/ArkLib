import itertools, math
from sympy import primitive_root, isprime
def roots(n,p,g): return [pow(g,j,p) for j in range(n)]
def K_at_w(n,p,w):
    g=pow(primitive_root(p),(p-1)//n,p); mu=roots(n,p,g)
    e1set=set(); cnt=0
    for S in itertools.combinations(range(n),w):
        s1=0;s2=0
        for i in S: v=mu[i]; s1+=v; s2+=v*v
        if (s1*s1-s2)%p==0 and s1%p!=0:
            cnt+=1; e1set.add((-pow(s1,p-2,p))%p)
    rem=set(e1set);K=0
    while rem: x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
    return cnt,len(e1set),K
n=64
for p in [n**4+1-((n**4)%n), None]:
    pass
p=n**4
while not ((p-1)%n==0 and isprime(p)): p+=1
print(f"=== n={n} p={p} shallow over-det census K(w), w=2..9 (resonance check w==0 mod 4) ===")
for w in range(2,10):
    if math.comb(n,w)>40_000_000:
        print(f"  w={w}: C({n},{w})={math.comb(n,w):,} skip"); continue
    cnt,dist,K=K_at_w(n,p,w)
    print(f"  w={w} w%4={w%4} K={K:4d} #bad={n*K:7d} {'RESONANCE n/4-1='+str(n//4-1) if K==n//4-1 else ('<=1 BUDGET-OK' if K<=1 else 'other')}",flush=True)
