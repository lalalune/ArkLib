import math
from collections import Counter

def subgroup_Fp(p, n):
    e=(p-1)//n
    for base in range(2,p):
        g=pow(base,e,p)
        if g!=1 and pow(g,n//2,p)!=1:
            G=[]; x=1
            for _ in range(n): G.append(x); x=x*g%p
            if len(set(G))==n: return G
    return None

def energy_add(G,p):
    r=Counter()
    for a in G:
        for b in G: r[(a+b)%p]+=1
    return sum(v*v for v in r.values())

# 1) exact 2-power threshold across primes: max mu with excess 0
print("=== F_p, 2-power subgroups: where does excess turn on? ===")
primes=[(40961,"5*2^13+1"),(786433,"3*2^18+1"),(7340033,"7*2^20+1"),(23068673,"11*2^21+1")]
for p,desc in primes:
    sp=math.sqrt(p)
    last0=None; first=None
    mu=2
    while (1<<mu) <= (p-1) and (1<<mu)<=4096:
        n=1<<mu
        if (p-1)%n: mu+=1; continue
        G=subgroup_Fp(p,n)
        if G is None: mu+=1; continue
        exc=energy_add(G,p)-(3*n*n-3*n)
        flag="ZERO" if exc==0 else f"exc={exc}"
        if exc==0: last0=n
        elif first is None: first=n
        print(f"  p={p}({desc}) n={n:5d}  n/sqrt(p)={n/sp:.3f}  n^2/p={n*n/p:.4f}  {flag}")
        mu+=1
    print(f"   -> last zero-excess n={last0}, first nonzero n={first}, sqrt(p)={sp:.0f}")
    print()

# 2) does it depend on 2-power, or any subgroup? test odd-order subgroups
print("=== F_p, does minimality need 2-power order? (p=786433, various n | p-1=3*2^18) ===")
p=786433
for n in [3,6,9,12,24,48,96,192,384,768,1536]:
    if (p-1)%n: continue
    G=subgroup_Fp(p,n)
    if G is None: continue
    exc=energy_add(G,p)-(3*n*n-3*n)
    print(f"  n={n:5d} (2-power={ (n&(n-1))==0 }) n^2/p={n*n/p:.4f} excess={exc}")
