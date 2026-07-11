# Compute actual B = max_{b!=0} |sum_{x in mu_n} e_p(bx)| at the bad primes vs good primes.
# Is "bad" a real large-B anomaly, or just moment-bound looseness (18th power amplifying)?
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
def gmu(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def Bval(p,n):
    roots=gmu(p,n)
    w=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
    best=0.0; bestb=0
    for b in range(1,p):
        s=0j
        for x in roots: s+=w[(b*x)%p]
        m=abs(s)
        if m>best: best=m; bestb=b
    return best,bestb
cases=[(64,33409,"BAD 63.8"),(32,5857,"BAD 1.25"),(64,7937,"BAD 151"),
       (64,33023,"good"),(128,186113,"good"),(32,5953,"good")]
print(f"{'n':<4}{'p':<8}{'tag':<10}{'B':<9}{'sqrt(n)':<9}{'B/sqrtn':<9}{'B/sqrt(2nlnp)':<14}{'n^{2/3}':<9}{'B/n^.667':<9}",flush=True)
for n,p,tag in cases:
    if not isprime(p): 
        print(f"{n} {p} not prime",flush=True); continue
    B,bb=Bval(p,n)
    sn=math.sqrt(n); wick=math.sqrt(2*n*math.log(p)); n23=n**(2/3)
    print(f"{n:<4}{p:<8}{tag:<10}{B:<9.2f}{sn:<9.2f}{B/sn:<9.3f}{B/wick:<14.3f}{n23:<9.2f}{B/n23:<9.3f}",flush=True)
