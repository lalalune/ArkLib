# NOVEL external handle: B = max_b|eta_b| = HOUSE of the algebraic integer eta.
# Norm N = prod_{cosets} eta_c (a cyclotomic integer / graph determinant) is Stickelberger-constrained.
# Test: is |N|^{1/m} ~ sqrt(n) (balanced => house bounded) and does norm+min-conjugate bound the house?
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def analyze(n,p):
    g0=primroot(p); g=pow(g0,(p-1)//n,p); roots=[pow(g,i,p) for i in range(n)]
    m=(p-1)//n
    # distinct eta values = one per coset rep g0^i, i=0..m-1
    etas=[]
    b=1
    for i in range(m):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in roots)
        etas.append(s); b=b*g0%p
    mags=[abs(e) for e in etas]
    B=max(mags); mn=min(mags)
    # log|N| = sum log|eta_c|; geometric mean = |N|^{1/m}
    logN=sum(math.log(mm) for mm in mags if mm>1e-9)
    gm=math.exp(logN/m)
    return B, mn, gm, m
print("n   p       B/sqrt(n)  min/sqrt(n)  geomMean/sqrt(n)  m=index   house/geomMean",flush=True)
for n in [8,16,32]:
    for p in [pp for pp in range(n+1, 3000, n) if isprime(pp)][:4]:
        B,mn,gm,m=analyze(n,p)
        sn=math.sqrt(n)
        print(f"{n:<4}{p:<8}{B/sn:<11.3f}{mn/sn:<13.3f}{gm/sn:<18.3f}{m:<10}{B/gm:<.3f}",flush=True)
