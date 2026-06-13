# #389 ADVERSARIAL deep-band refutation probe (2026-06-13): can any deep-band (a=rm+1) single-poly
# word exceed budget 2^r*C(2^{mu-1},r)? RESULT: NO -- adversarial trapped-set words give maxbad ~3-5
# for n=8 (r=2), FAR below budget 24. KKH26's large count is at the CEILING (q-dependent 17->25->28),
# not deep band (deg rm < rm+1 => zero deep bad). So CensusDomination holds ROBUSTLY; residual is pure
# proof tightness (provable C(n,k+1)=28 vs true O(n)~3-5) = the line-ball incidence. Pin NOT refuted.
import itertools, random
from math import comb
def pf(n):
    f=[];d=2
    while d*d<=n:
        while n%d==0:f.append(d);n//=d
        d+=1
    if n>1:f.append(n)
    return f
def gen(p,n):
    for a in range(2,p):
        if pow(a,n,p)==1 and all(pow(a,n//q,p)!=1 for q in set(pf(n))):return a
def interp(Q,pts,p):
    m=len(pts)
    def qe(x):
        r=0
        for c in reversed(Q):r=(r*x+c)%p
        return r%p
    A=[[pow(pts[i],j,p) for j in range(m)]+[qe(pts[i])] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if A[rr][col]%p),None)
        if piv is None:return None
        A[col],A[piv]=A[piv],A[col]
        inv=pow(A[col][col],p-2,p);A[col]=[(v*inv)%p for v in A[col]]
        for rr in range(m):
            if rr!=col and A[rr][col]%p:
                f=A[rr][col];A[rr]=[(A[rr][k]-f*A[col][k])%p for k in range(m+1)]
    return [A[i][m]%p for i in range(m)]
def bc(Q,mun,n,r,p):
    bad=set()
    for S in itertools.combinations(range(n),r+1):
        c=interp(Q,[mun[i] for i in S],p)
        if c and (c[r] if r<len(c) else 0)%p==0:
            bad.add((-(c[r-1] if r-1<len(c) else 0))%p)
    return len(bad)
def mA(A,mun,p):
    co=[1]
    for i in A:
        z=mun[i];nw=[0]*(len(co)+1)
        for j,cc in enumerate(co):
            nw[j]=(nw[j]-cc*z)%p;nw[j+1]=(nw[j+1]+cc)%p
        co=nw
    return co
def run(p,mu,r):
    n=1<<mu;g=gen(p,n);mun=[pow(g,j,p) for j in range(n)]
    bud=(1<<r)*comb(2**(mu-1),r);mx=0;random.seed(0)
    for _ in range(4000):
        Q=[random.randrange(p) for _ in range(2*r+1)]
        if Q[2*r]==0:Q[2*r]=1
        mx=max(mx,bc(Q,mun,n,r,p))
    for A in itertools.combinations(range(n),2*r):
        co=mA(A,mun,p)
        for _ in range(40):
            P0=[random.randrange(p) for _ in range(r)];cm=random.randrange(1,p)
            Q=[((P0[j] if j<r else 0)+cm*(co[j] if j<len(co) else 0))%p for j in range(2*r+1)]
            mx=max(mx,bc(Q,mun,n,r,p))
    print(f"p={p} n={n} r={r} maxbad={mx} budget={bud} C(n,r)={comb(n,r)} EXCEEDS={mx>bud}",flush=True)
for p in [97,193,389,769,1543,3089,6173]:
    run(p,3,2)
