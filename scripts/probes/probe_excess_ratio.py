def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def subgroup(p,n):
    for g in range(2,p):
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(g,i,p) for i in range(n)]
    return None
def energy(p,n):
    G=subgroup(p,n)
    if G is None or len(set(G))!=n: return None
    from collections import Counter
    r=Counter()
    for a in G:
        for b in G: r[(a+b)%p]+=1
    return sum(v*v for v in r.values())
# Track max E/n^2 and max excess/n^2 over ALL even n, ALL proper primes n^2<p (bounded scan)
maxE=0; maxEcase=None; maxexc=0; maxexccase=None
# also test the BOUNDARY n ~ sqrt(p) (n^2 just below p) where energy might spike
boundary=[]
for p in range(11,2500):
    if not is_prime(p): continue
    for n in range(6, int((p-1)**0.5)+1, 2):
        if (p-1)%n: continue
        e=energy(p,n)
        if e is None: continue
        Eratio=e/(n*n); excratio=(e-(3*n*n-3*n))/(n*n)
        if Eratio>maxE: maxE=Eratio; maxEcase=(p,n,e)
        if excratio>maxexc: maxexc=excratio; maxexccase=(p,n,e)
        # boundary: n^2 in (p/2, p)
        if n*n > p*0.5: boundary.append((p,n,round(Eratio,2),round(excratio,2)))
print(f"MAX E/n^2 = {maxE:.3f} at (p,n,E)={maxEcase}")
print(f"MAX excess/n^2 = {maxexc:.3f} at (p,n,E)={maxexccase}")
print(f"\nBoundary cases n^2>p/2 (closest to n~sqrt(p)): E/n^2, excess/n^2")
for p,n,Er,exc in sorted(boundary, key=lambda x:-x[3])[:15]:
    print(f"  p={p:>5} n={n:>3}  n^2/p={n*n/p:.2f}  E/n^2={Er:>5}  excess/n^2={exc:>5}")
