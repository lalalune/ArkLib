import itertools

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
def isprime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def mun(n,p):
    g=primitive_root(p); b=pow(g,(p-1)//n,p)
    return [pow(b,i,p) for i in range(n)]
def all_primes_for_n(n, count, lo=None):
    ps=[]; p=(lo if lo else n+1)
    while len(ps)<count:
        if (p-1)%n==0 and isprime(p): ps.append(p)
        p+=1
    return ps

# Find the smallest prime threshold above which ZERO decomposition-violators for w=5.
print("=== threshold: smallest p (n|p-1) above which 0 violators for all larger primes ===")
for n in [8,12,16,20]:
    if n%4: continue
    h=n//4
    ps=all_primes_for_n(n, 40, lo=n+1)
    results=[]
    for p in ps:
        mu=mun(n,p); viol=0
        for S in itertools.combinations(range(n),5):
            vals=[mu[i] for i in S]
            e1=sum(vals)%p
            if e1==0: continue
            p2=sum((x*x)%p for x in vals)%p
            if (e1*e1-p2)%p!=0: continue
            found=False
            for j in range(h):
                cs={j,(j+h)%n,(j+2*h)%n,(j+3*h)%n}
                if cs<=set(S): found=True; break
            if not found: viol+=1
        results.append((p,viol))
    # largest prime with a violator
    last_bad=max([p for (p,v) in results if v>0], default=None)
    print(f"n={n}: largest violating prime = {last_bad}; n^2={n*n}, n^3={n**3}.  Tail: {[(p,v) for (p,v) in results if p> (last_bad or 0)][:3]}")
    print(f"      all: {[(p,v) for (p,v) in results if v>0]}")
