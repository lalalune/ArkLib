import math, cmath
def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def factor_small(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def find_prime(t,mod):
    k=max(1,round(t/mod))
    for d in range(0,400000):
        for s in (1,-1):
            kk=k+s*d
            if kk<1: continue
            p=kk*mod+1
            if p>3 and is_prime(p): return p
def sub(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); e=[];x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e
def periods(e,p):
    w=2*math.pi/p
    return [sum(cmath.exp(1j*w*((b*x)%p)) for x in e) for b in range(p)]
# Test: is the GENUINE (DC + antipodal-reality subtracted) deep structure thinness-essential?
# eta_b is REAL (mu_n negation-closed). Decompose sum_{b!=0} eta_b^r.
# Compare |sum_{b!=0} eta_b^r| / (p * M^r) -- the normalized deep cancellation (prize wants this small).
print("Normalized deep period-power sum: C_r = |sum_{b!=0} eta_b^r| / ((p-1) M^r)")
print("(=1 means no cancellation/aligned; ->0 means strong cancellation. Prize=strong cancellation, all r.)")
for n in [8,16]:
    print(f"== n={n} ==")
    for beta in [2.5,4.0,4.5]:
        if n==16 and beta>4.0: continue
        p=find_prime(int(n**beta),n)
        if not p: continue
        ab=math.log(p)/math.log(n)
        e=sub(n,p); eta=periods(e,p)
        M=max(abs(eta[b]) for b in range(1,p))
        cells=[]
        for r in range(2,2*int(math.log2(n))+3):
            tot=sum(eta[b]**r for b in range(1,p))
            C=abs(tot)/((p-1)*M**r)
            cells.append(f"r{r}:{C:.4f}")
        print(f"  beta={ab:.2f} p={p} M={M:.2f}: "+" ".join(cells))
