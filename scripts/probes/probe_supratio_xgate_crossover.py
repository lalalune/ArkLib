import cmath, math
from math import log, sqrt
SQRT2=sqrt(2)
def isprime(m):
    if m<2:return False
    if m%2==0:return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0:continue
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def Msup(p,n,g):
    m=(p-1)//n
    h=pow(g,m,p); mun=[pow(h,j,p) for j in range(n)]
    w=2*math.pi/p; best=-1.0; bt=1
    for t in range(m):
        s=0j
        for y in mun: s+=cmath.exp(1j*w*((bt*y)%p))
        a=abs(s)
        if a>best: best=a
        bt=(bt*g)%p
    return best

# KEY HYPOTHESIS: per-level ratio M(n)/M(n/2) is ~2 when n < ln(m) [trivial regime, M~n]
# and ~sqrt2 when n > ln(m) [cancellation regime, M~sqrt(n ln m)].
# At fixed prime p, climb tower; record ratio against x = n / ln(m).
NTOP=512
cands=[]
p=NTOP+1; cnt=0
while cnt<5000 and p<50_000_000:
    if isprime(p) and (p-1)%NTOP==0:
        cands.append(p); cnt+=1
    p+=1
import random
random.seed(11)
random.shuffle(cands)
# we want a RANGE of beta at top, and small m so fast
cands=[p for p in cands if (p-1)//NTOP<=4000][:6]

print("HYPOTHESIS: ratio ~2 if n<ln(m), ratio ~sqrt2 if n>ln(m).")
print("Tracking x = n/ln(m) vs per-level ratio (same prime).\n")
rows=[]
for p in sorted(cands):
    g=primroot(p)
    print(f"p={p}:")
    print(f"  {'n':>4} {'m':>8} {'lnm':>5} {'n/lnm':>6} {'M(n)':>8} {'M(n)/n':>7} {'ratio':>6}")
    Mprev=None
    n=2
    while n<=NTOP and (p-1)%n==0:
        M=Msup(p,n,g); m=(p-1)//n; lnm=log(m)
        x=n/lnm
        rr=M/Mprev if Mprev else float('nan')
        if Mprev: rows.append((x, rr, n, p))
        print(f"  {n:>4} {m:>8} {lnm:>5.2f} {x:>6.2f} {M:>8.3f} {M/n:>7.4f} {('%.4f'%rr) if Mprev else '  -  ':>6}")
        Mprev=M; n*=2
    print()

print("=== per-level ratio bucketed by x=n/ln(m) ===")
print("  (if hypothesis true: x<<1 => ratio~2, x>>1 => ratio~sqrt2=1.414)")
for lo,hi in [(0,0.25),(0.25,0.5),(0.5,1),(1,2),(2,4),(4,8),(8,100)]:
    sub=[r for r in rows if lo<=r[0]<hi]
    if sub:
        rs=[r[1] for r in sub]
        print(f"  x in [{lo},{hi}): n={len(sub):>3} mean_ratio={sum(rs)/len(rs):.4f} min={min(rs):.4f} max={max(rs):.4f}")
