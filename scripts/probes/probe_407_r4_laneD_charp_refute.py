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

# Test the DECOMPOSE direction across MANY primes (including small/structured ones near n)
# to see if w=5 e2=0 ever has a set NOT of the form (mu_4-coset)+point.
# This determines whether K=1 (single coset) can FAIL at structured chars.
def all_primes_for_n(n, count, lo=None):
    ps=[]; p=(lo if lo else n+1)
    while len(ps)<count:
        if (p-1)%n==0 and isprime(p): ps.append(p)
        p+=1
    return ps

print("=== DECOMPOSE direction stress test across many primes (small + prize) ===")
for n in [8,12,16]:
    if n%4: continue
    h=n//4
    # include SMALL primes (structured, possible char-p coincidences) AND prize primes
    small=all_primes_for_n(n, 8, lo=n+1)
    prize=all_primes_for_n(n, 3, lo=n**3)
    bad=[]
    Ks=[]
    for p in small+prize:
        mu=mun(n,p)
        e1vals=[]; violators=0
        for S in itertools.combinations(range(n),5):
            vals=[mu[i] for i in S]
            e1=sum(vals)%p
            if e1==0: continue
            p2=sum((x*x)%p for x in vals)%p
            if (e1*e1-p2)%p!=0: continue
            e1vals.append(e1)
            found=False
            for j in range(h):
                coset={j,(j+h)%n,(j+2*h)%n,(j+3*h)%n}
                if coset<=set(S): found=True; break
            if not found: violators+=1
        rem=set(e1vals); K=0
        while rem:
            x=next(iter(rem)); rem-=set((u*x)%p for u in mu); K+=1
        Ks.append((p,K,violators))
        if violators: bad.append(p)
    print(f"n={n}: K values & decomposition-violators across {len(small+prize)} primes:")
    for (p,K,v) in Ks:
        flag=" <-- prize" if p>=n**3 else ""
        vflag=f"  VIOLATORS={v}!!!" if v else ""
        print(f"    p={p:8d}: K={K}{vflag}{flag}")
