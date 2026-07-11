import cmath, math
def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def find_primes(n, count, minratio=4):
    out=[]; k=minratio
    while len(out)<count and k<minratio+50000:
        p=n*k+1
        if p>3 and all(p%d for d in range(2,int(p**0.5)+1)): out.append(p)
        k+=1
    return out
def munit(p,n):
    m=(p-1)//n
    for a in range(2,p):
        h=pow(a,m,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in prime_factors(n)):
            G=[]; v=1
            for _ in range(n): G.append(v); v=v*h%p
            return G
    return None
def ep(p): return lambda t: cmath.exp(2j*math.pi*(t%p)/p)
def eta(G,c,p,w): return sum(w((c*x)%p) for x in G)
def inv(a,p): return pow(a,p-2,p)

# HYPOTHESIS: eta_{b(zeta^{-1}-1)} == conj( eta_{b(zeta-1)} ) for each zeta in subgroup G.
cases=[]
for n in [8,16,32]:
    for p in find_primes(n,2,4): cases.append((n,p))
cases += [(16,65537),(32,65537),(16,257)]

for n,p in cases:
    G=munit(p,n)
    if G is None: continue
    w=ep(p)
    maxpair=0; maxscale=0
    for b in [1,3,(p-1)//2,p-2]:
        b%=p
        if b==0: continue
        for z in G:
            if z==1: continue
            zi=inv(z,p)
            lhs=eta(G,(b*(zi-1))%p,p,w)
            rhs=eta(G,(b*(z-1))%p,p,w).conjugate()
            maxpair=max(maxpair,abs(lhs-rhs))
            c=(b*(z-1))%p
            for u in G[1:2]:
                maxscale=max(maxscale,abs(eta(G,c,p,w)-eta(G,(c*u)%p,p,w)))
    print(f"n={n:3d} p={p:7d}  pair_err={maxpair:.2e}  PAIR={'HOLDS' if maxpair<1e-9 else 'FAILS'}   scaleinv_err={maxscale:.2e}")
