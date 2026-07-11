import itertools, cmath, math
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
def E_char0(n,r):
    mu=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
    s=Counter()
    for x in itertools.product(range(n),repeat=r):
        z=sum(mu[i] for i in x); s[(round(z.real,4),round(z.imag,4))]+=1
    return sum(c*c for c in s.values())
# THE corrected-target question: does the SUP-bound margin survive as depth r grows?
# n=16 thin primes p>=65536 (beta>=4), r=4,5,6 (above onset r0~4). Track max_p W_r/E0.
# If max W_r/E0 stays bounded well below 1 as r grows => sup bound survives depth (prize evidence).
# If it climbs toward 1 => warning the sup bound degrades at depth.
n=16
print(f"n={n}: SUP-bound depth trend.  max_p (W_r/E0) over thin primes p>=65536, r=4..6.")
print(f"{'r':>3}{'#primes':>9}{'max W_r/E0':>14}{'at p':>10}{'mean W_r/E0':>14}{'#nonzero':>10}")
primes=[]
p=65537
while len(primes)<10:
    if p%n==1 and isprime(p): primes.append(p)
    p+=2
for r in [4,5,6]:
    E0=E_char0(n,r)
    rows=[]
    for p in primes:
        mu=mu_Fp(n,p)
        w=E_charP(mu,p,r)-E0
        rows.append((p,w/E0,w))
    mx=max(rows,key=lambda x:x[1])
    mean=sum(x[1] for x in rows)/len(rows)
    nz=sum(1 for x in rows if x[2]!=0)
    print(f"{r:>3}{len(rows):>9}{mx[1]:>14.6f}{mx[0]:>10}{mean:>14.6f}{nz:>10}")
print("\ninterpretation: trend of max W_r/E0 across r=4,5,6 (does the worst-case margin to 1 hold?)")
