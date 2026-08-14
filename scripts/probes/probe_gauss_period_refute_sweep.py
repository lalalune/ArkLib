import numpy as np, math
from sympy import isprime
def primes_cong1(n, lo, hi, count):
    out=[]; p = lo + ((1-(lo%n))%n)
    while p<=hi and len(out)<count:
        if isprime(p): out.append(p)
        p+=n
    return out
def order_elt(p,n):
    def pf(m):
        f=set();d=2
        while d*d<=m:
            while m%d==0:f.add(d);m//=d
            d+=1
        if m>1:f.add(m)
        return f
    for g in range(2,p):
        z=pow(g,(p-1)//n,p)
        if all(pow(z,n//q,p)!=1 for q in pf(n)):return z
    raise RuntimeError
def maxperiod(p,n):
    z=order_elt(p,n); ind=np.zeros(p)
    for j in range(n): ind[pow(z,j,p)]=1.0
    F=np.fft.fft(ind); return float(np.abs(F[1:]).max())
print("Refutation sweep: C = max_b|η_b| / √(n·ln(p/n)).  conj: C bounded (≲1.5). multiple primes per n.",flush=True)
print(f"{'n':>5}{'#primes':>8}{'C_min':>8}{'C_mean':>8}{'C_MAX':>8}{'argmax p':>11}",flush=True)
worst_overall=0; worst_pn=None
for mu in [3,4,5,6]:
    n=2**mu
    # sample primes p≡1 mod n in [n^4, 3 n^4] (prize regime β≈4), capped count for speed
    cnt = {3:40,4:25,5:12,6:4}[mu]
    ps=primes_cong1(n, n**4, 3*n**4, cnt)
    Cs=[]
    for p in ps:
        C=maxperiod(p,n)/math.sqrt(n*math.log(p/n)); Cs.append((C,p))
        if C>worst_overall: worst_overall=C; worst_pn=(p,n)
    Cs.sort()
    import statistics
    cvals=[c for c,_ in Cs]
    cmax,pmax=max(Cs)
    print(f"{n:>5}{len(ps):>8}{min(cvals):>8.3f}{statistics.mean(cvals):>8.3f}{cmax:>8.3f}{pmax:>11}",flush=True)
print(f"\nWORST overall C = {worst_overall:.4f} at (p,n)={worst_pn}",flush=True)
print("β-variation (n=16, p near n^3, n^4, n^5):",flush=True)
n=16
for beta in [3,4,5]:
    ps=primes_cong1(n, n**beta, 2*n**beta, 3)
    for p in ps[:1]:
        C=maxperiod(p,n)/math.sqrt(n*math.log(p/n))
        print(f"  β≈{beta}: p={p}, C={C:.3f}",flush=True)
