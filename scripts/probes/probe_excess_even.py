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
def excess(p,n):
    G=subgroup(p,n)
    if G is None or len(set(G))!=n: return None
    from collections import Counter
    r=Counter()
    for a in G:
        for b in G: r[(a+b)%p]+=1
    E=sum(v*v for v in r.values())
    return E-(3*n*n-3*n)
# For each even n, test SEVERAL proper primes p (n^2 < p), report excess for each
print("even n: excess across several proper primes p (n^2<p), -1 in mu_n required")
for n in range(6,33,2):
    vals=[]
    cnt=0
    for p in range(n*n+1, n*n*40):
        if not is_prime(p): continue
        if (p-1)%n: continue
        e=excess(p,n)
        if e is None: continue
        vals.append((p,e))
        cnt+=1
        if cnt>=6: break
    nz=[f"p{p}:{e:+d}" for p,e in vals if e!=0]
    allzero = all(e==0 for _,e in vals)
    print(f"n={n:>3}  {'ALL ZERO (Sidon!)' if allzero else 'NONZERO: '+' '.join(nz)}   samples={[e for _,e in vals]}")
