# General-k shallow over-det e2=0 census: pencil x^k + alpha x^{k+2}, agreement w=k+2,
# alpha = -1/e1(S), e2(S)=0 the over-det constraint. K = #dilation-orbits of e1.
# Test K(n, w=k+2) for k=2,3,4,5 at fixed n => does the n/4-1 resonance persist / depend on k?
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
print("General-k shallow e2=0 census K(n, w=k+2). Does K depend on k or only on w=k+2?")
print("(e2=0 is the SAME quadratic constraint for any k; w=k+2 is the only k-dependence => K should depend on w only)")
for n in [16,32]:
    p=n**4
    while not ((p-1)%n==0 and isprime(p)): p+=1
    print(f"\n=== n={n} p={p} ===")
    for k in [2,3,4,5,6]:
        w=k+2
        if w>n: continue
        if math.comb(n,w) > 30_000_000:
            print(f"  k={k} w={w}: C({n},{w})={math.comb(n,w):,} too big, skip"); continue
        cnt,dist,K=K_at_w(n,p,w)
        print(f"  k={k} w=k+2={w}: K={K:4d} #bad=n*K={n*K:6d} delta=1-w/n={1-w/n:.3f} cap=1-k/n={1-k/n:.3f} {'IN-WINDOW' if (1-w/n)<(1-k/n) else 'ABOVE-CAP'} | n/4-1={n//4-1}")
