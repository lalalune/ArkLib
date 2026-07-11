#!/usr/bin/env python3
"""
Conditions-rank collapse on A = mu_n ∩ (mu_n + c), but in the LARGE-|A| regime
(the only regime where the HBK degeneracy can show). Pick c to MAXIMIZE |A|.
Measure effective GF(p) rank of the order-M Hasse conditions; if rho << |A|*M
with a clean LAW, that law is the brick. If rho = min(|A|*M, D) always, the
generic wall (StepanovGenericInsufficiency) is reconfirmed on the diagonal too -> NEGATIVE,
log once, do NOT formalize.
"""
import sympy as sp
from sympy import binomial

def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def find_gen(p,n):
    pf=prime_factors(n)
    for c in range(2,p):
        if pow(c,n,p)==1 and all(pow(c,n//q,p)!=1 for q in pf): return c
    raise RuntimeError
def mu_n(p,n):
    g=find_gen(p,n); return [pow(g,i,p) for i in range(n)]
def find_prime(n,beta):
    k=max(1,n**beta//n)
    while True:
        p=k*n+1
        if p>2*n**3 and sp.isprime(p): return p
        k+=1
def rank_gfp(rows,p):
    rows=[r[:] for r in rows]; nr=len(rows); nc=len(rows[0]) if rows else 0; r=0; rank=0
    for col in range(nc):
        piv=None
        for i in range(r,nr):
            if rows[i][col]%p!=0: piv=i; break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][col],p-2,p); rows[r]=[(x*inv)%p for x in rows[r]]
        for i in range(nr):
            if i!=r and rows[i][col]%p!=0:
                f=rows[i][col]; rows[i]=[(rows[i][k]-f*rows[r][k])%p for k in range(nc)]
        r+=1; rank+=1
        if r==nr: break
    return rank
def conditions_rank(A,M,D,p):
    rows=[]
    for a in A:
        for j in range(M):
            row=[(int(binomial(e,j)%p)*pow(a,e-j,p))%p if e>=j else 0 for e in range(D)]
            rows.append(row)
    return rank_gfp(rows,p),len(rows)

print("DIAGONAL-regime conditions-rank collapse probe (max |A|)")
print("="*88)
for n in [8,16]:
    p=find_prime(n,4); G=set(mu_n(p,n))
    best=None
    for c in range(1,p):
        A=[x for x in G if ((x-c)%p) in G]
        if best is None or len(A)>len(best[1]): best=(c,A)
    c,A=best; r=len(A)
    print(f"\nn={n} p={p} c={c} MAX|A|=r(c)={r}  (order2 bound (n+1)/2={(n+1)//2})")
    print(f"   {'M':>2} {'|A|*M':>6} {'rho':>5} {'D=needed(rho+1)':>15} {'r<=deg/M':>9} {'collapse?':>9}")
    for M in [1,2,3,4]:
        Dtest=r*M+3
        rho,nc=conditions_rank(A,M,Dtest,p)
        minD=rho+1; implied=(minD-1)/M
        coll = "YES" if rho < min(r*M, Dtest) else "no"
        print(f"   {M:>2} {r*M:>6} {rho:>5} {minD:>15} {implied:>9.2f} {coll:>9}")
