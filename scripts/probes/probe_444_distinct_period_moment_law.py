import cmath, math

def prime_factors(m):
    f=[]; d=2
    while d*d<=m:
        while m%d==0: f.append(d); m//=d
        d+=1
    if m>1: f.append(m)
    return f

def subgroup(p,n):
    assert (p-1)%n==0
    pf=set(prime_factors(p-1)); g=None
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in pf): g=c; break
    h=pow(g,(p-1)//n,p)
    return sorted({pow(h,k,p) for k in range(n)})

def eta(p,S,b):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((b*x)%p)) for x in S)

def N0(p,S,r):
    cur=[0]*p; cur[0]=1
    for _ in range(r):
        nxt=[0]*p
        for a in range(p):
            ca=cur[a]
            if ca:
                for x in S: nxt[(a+x)%p]+=ca
        cur=nxt
    return cur[0]

# distinct-period law: pick ONE rep per mu_n-coset of F_p^*, sum eta_i^r over the m reps.
# claim: sum_{i in reps} eta_i^r == (p/n)*N0 - n^(r-1)
cases=[(17,4),(97,8),(193,8),(257,16),(7681,16),(12289,16),(40961,16)]
for p,n in cases:
    if (p-1)%n: continue
    S=subgroup(p,n)
    # cosets of mu_n in F_p^*: partition nonzero residues by mu_n-orbit
    seen=set(); reps=[]
    for b in range(1,p):
        if b in seen: continue
        orbit={ (b*x)%p for x in S }
        seen|=orbit; reps.append(b)
    m=(p-1)//n
    assert len(reps)==m, (len(reps),m)
    for r in [1,2,3,4,5]:
        lhs=sum(eta(p,S,b)**r for b in reps)
        nn=N0(p,S,r)
        rhs=(p/n)*nn - n**(r-1)
        ok=abs(lhs.imag)<1e-5 and abs(lhs.real-rhs)<1e-4*max(1,abs(rhs))
        print(f"p={p} n={n} m={m} r={r}: Re(sum_reps eta^r)={lhs.real:+.3f} (q/n)N0-n^(r-1)={rhs:+.3f} N0={nn} {'OK' if ok else 'FAIL'}")
