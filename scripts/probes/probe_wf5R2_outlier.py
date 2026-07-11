import numpy as np
from math import log, sqrt

def gauss_abs(p, n):
    pm1=p-1
    def factor(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    fs=factor(pm1)
    g=2
    while not all(pow(g,pm1//q,p)!=1 for q in fs): g+=1
    h=pow(g,pm1//n,p)
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.float64)
    b=np.arange(1,p,dtype=np.float64)
    ang=2*np.pi*np.outer(b,mu)/p
    S=np.cos(ang).sum(1)+1j*np.sin(ang).sum(1)
    return np.abs(S)

# Question: is M(n) an ISOLATED outlier above edge, or does the whole top of the bulk sit above 2sqrt(n-1)?
# Count fraction of b with |S_b| > 2 sqrt(n-1), and ratio of top-2 to top.
print(f"{'n':>4} {'p':>7} {'M':>8} {'edge':>7} {'#>edge':>7} {'frac>edge':>9} {'2nd/M':>6} {'M/sqrt(n)':>9}")
for n,p in [(8,1129),(8,10169),(16,1153),(16,65537),(32,1217),(32,65921),(64,65921),(128,65921)]:
    if (p-1)%n: continue
    a=gauss_abs(p,n)
    a_sorted=np.sort(a)[::-1]
    M=a_sorted[0]; edge=2*sqrt(n-1)
    nover=(a>edge).sum(); frac=nover/len(a)
    print(f"{n:>4} {p:>7} {M:8.3f} {edge:7.3f} {nover:>7} {frac:9.4f} {a_sorted[1]/M:6.3f} {M/sqrt(n):9.3f}")

# The KM "bulk edge" 2 sqrt(n-1) is the edge for the DEGREE-n tree. But Cay(F_p,mu_n) is NOT tree-like:
# girth is small (4-cycles abound from x+y=x'+y'), so it's NOT Ramanujan-like. The outlier band is real.
# Correct picture (Kunisky): bulk ESD -> KM, but extreme eigenvalue has a DEFECT = M(n)-2sqrt(n-1).
# That defect IS the unknown. So edge-rigidity for the extreme eval is exactly the open problem, NOT closed.

# Check: does M^{2k} <= p * E_k give the prize bound at optimal k? E_k = (1/p) sum_b |S_b|^{2k} (b!=0 incl)
print()
print("Moment-method test: best bound min_k (p*E_k)^{1/2k} vs M and vs prize")
for n,p in [(8,10169),(16,65537),(32,65921),(64,65921),(128,65921)]:
    if (p-1)%n: continue
    a=gauss_abs(p,n); a2=a**2
    M=a.max(); prize=sqrt(n*log(p/n))
    best=1e18;bk=0
    for k in range(1,40):
        Ek=(a2**k).mean()   # (1/(p-1)) sum |S_b|^{2k}
        est=(p*Ek)**(1.0/(2*k))   # crude moment bound on max
        if est<best: best=est;bk=k
    print(f"n={n:4} p={p:7} M={M:8.3f} prize={prize:8.3f} momentEst={best:8.3f}(k={bk}) ratio_est/prize={best/prize:.3f}")
