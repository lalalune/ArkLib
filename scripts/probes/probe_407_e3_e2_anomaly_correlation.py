from collections import Counter
import itertools
def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def subgroup(p,n):
    for cand in range(2,p):
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(cand,i,p) for i in range(n)]
def is_prime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def E2(G,p):
    N=Counter()
    for a in G:
        for b in G: N[(a+b)%p]+=1
    return sum(v*v for v in N.values())
def E3(G,p):
    N=Counter()
    for c in itertools.product(G,repeat=3): N[sum(c)%p]+=1
    return sum(v*v for v in N.values())
# Test HYPOTHESIS: E3 spike is DRIVEN by E2 additive-energy anomaly (a 2nd-order/random artifact),
# NOT a thinness mechanism. If so: E3/Wick3 tracks (E2/Wick2)^something => moment route is self-similar
# => the spike is exactly the route-eliminated 2nd-order signal, confirming meta-thm, NOT a CORE lever.
n=32
wick2=2*n*n  # leading random E2 (neg-closed)
wick3=15*n**3
print(f"n={n}  testing E3-spike <-> E2-anomaly correlation (rule-3 thin-essential check)")
print(f"{'p':>7} {'E2':>6} {'E2/2n^2':>8} {'E3':>8} {'E3/Wick3':>9} {'corr?':>6}")
found=0
for m in range(2,4000):
    p=m*n+1
    if not is_prime(p) or p<n**3: continue
    G=subgroup(p,n)
    if G is None: continue
    e2=E2(G,p); e3=E3(G,p)
    r2=e2/wick2; r3=e3/wick3
    flag="SPIKE" if r3>1.0 else ""
    print(f"{p:>7} {e2:>6} {r2:>8.3f} {e3:>8} {r3:>9.3f} {flag:>6}")
    found+=1
    if found>=12: break
