import itertools, math
from collections import Counter
def isprime(k):
    if k<2: return False
    if k%2==0: return k==2
    i=3
    while i*i<=k:
        if k%i==0: return False
        i+=2
    return True
def mu_Fp(n,p):
    def order(a,p):
        o=1;x=a%p
        while x!=1: x=(x*a)%p;o+=1
        return o
    g=2
    while order(g,p)!=p-1: g+=1
    h=pow(g,(p-1)//n,p)
    return [pow(h,k,p) for k in range(n)]
def E_charP(mu,p,r):
    s=Counter()
    for x in itertools.product(mu,repeat=r): s[sum(x)%p]+=1
    return sum(c*c for c in s.values())
def dfact(m):  # (2r-1)!!
    pr=1
    while m>0: pr*=m; m-=2
    return pr
# CORRECT prize criterion: rho_r(p) = S_r/((p-1)*Wick), S_r = p*E_r - n^{2r}, Wick=(2r-1)!!*n^r.
# This is avg_{b!=0}|eta_b|^{2r} / Wick.  Prize wants rho_r <= 1 (gives M<=sqrt(e)*sqrt(2rn) at saddle).
n=16
print(f"n={n}: CORRECT DC-subtracted criterion rho_r=(p*E_r-n^2r)/((p-1)*(2r-1)!!*n^r) over thin primes p>=65536.")
print(f"prize wants rho_r<=1.  (saddle for these p is r~ln p~11; track trend r=4,5,6)")
print(f"{'r':>3}{'Wick':>16}{'max rho_r':>12}{'at p':>9}{'mean rho_r':>12}{'min rho_r':>12}")
primes=[]
p=65537
while len(primes)<10:
    if p%n==1 and isprime(p): primes.append(p)
    p+=2
for r in [4,5,6]:
    Wick=dfact(2*r-1)*n**r
    n2r=n**(2*r)
    rows=[]
    for p in primes:
        mu=mu_Fp(n,p)
        Er=E_charP(mu,p,r)
        Sr=p*Er - n2r
        rho=Sr/((p-1)*Wick)
        rows.append((p,rho))
    mx=max(rows,key=lambda x:x[1]); mn=min(rows,key=lambda x:x[1])
    mean=sum(x[1] for x in rows)/len(rows)
    print(f"{r:>3}{Wick:>16}{mx[1]:>12.5f}{mx[0]:>9}{mean:>12.5f}{mn[1]:>12.5f}")
print("\nIf max rho_r stays < 1 and ~flat across r => correctly-normalized sup bound holds with margin at depth.")
