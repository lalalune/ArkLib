# PROBE (rule 2): distinct-period SECOND MOMENT exact value over PROPER thin mu_n.
# Claim: sum_{t in T} ||eta_t||^2 = q - n  (T = coset transversal of F_p* / mu_n)
# Equivalently n * sum_T ||eta_t||^2 = q*n - n^2 = sum_{b!=0} ||eta_b||^2.
# avg ||eta_t||^2 = (q-n)/m = n exactly (m = (q-1)/n distinct periods).
# NEVER n = q-1. PROPER subgroups only. multi-prime incl p >> n^3 and Fermat.
import cmath, math

def prime_factors(m):
    fac=set(); d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    return fac

def primitive_root(p):
    phi=p-1; fac=prime_factors(phi)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    raise RuntimeError

def test(p,n):
    assert (p-1)%n==0
    assert n<p-1, "PROPER only"
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)
    H=set(); x=1
    for _ in range(n): H.add(x); x=(x*h)%p
    assert len(H)==n
    w=cmath.exp(2j*math.pi/p)
    def eta(b): return sum(w**((b*y)%p) for y in H)
    full=sum(abs(eta(b))**2 for b in range(p))
    nz=sum(abs(eta(b))**2 for b in range(1,p))
    seen=set(); reps=[]
    for b in range(1,p):
        if b in seen: continue
        reps.append(b)
        for y in H: seen.add((b*y)%p)
    m=len(reps)
    dsm=sum(abs(eta(t))**2 for t in reps)
    return full,nz,dsm,m

cases=[(17,2),(17,4),(17,8),(41,4),(41,8),(97,8),(97,16),(73,8),(257,16),(4129,16),(40961,16),(7681,16),(12289,16)]
print(f"{'p':>7}{'n':>5}{'m':>6} | {'full':>12}{'qn':>9} | {'nz':>12}{'qn-n2':>9} | {'distinct':>12}{'q-n':>8} avg  OK")
allok=True
for p,n in cases:
    if (p-1)%n!=0 or n>=p-1:
        print(f"  skip {p},{n}"); continue
    full,nz,dsm,m=test(p,n)
    qn=p*n; qnn2=p*n-n*n; qmn=p-n
    ok=abs(full-qn)<1e-2 and abs(nz-qnn2)<1e-2 and abs(dsm-qmn)<1e-2 and m==(p-1)//n
    allok=allok and ok
    print(f"{p:>7}{n:>5}{m:>6} | {full:>12.3f}{qn:>9} | {nz:>12.3f}{qnn2:>9} | {dsm:>12.3f}{qmn:>8} {dsm/m:>5.2f} {'PASS' if ok else 'FAIL'}")
print("ALL PASS" if allok else "SOME FAIL")
