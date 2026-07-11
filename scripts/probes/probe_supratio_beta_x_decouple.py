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
import statistics
# DECOUPLING TEST: collect (x=n/lnm, beta, ratio) triples. partial corr.
# If ratio is driven by x not beta: corr(x,ratio) strong negative, corr(beta,ratio|x) ~0.
NTOP=128
cands=[]; p=NTOP+1; cnt=0
while cnt<8000 and p<100_000_000:
    if isprime(p) and (p-1)%NTOP==0:
        cands.append(p); cnt+=1
    p+=1
import random
random.seed(5)
random.shuffle(cands)
cands=[p for p in cands if (p-1)//NTOP<=2500][:200]
rows=[]
for p in cands:
    g=primroot(p)
    Ms={}; n=2
    while n<=NTOP and (p-1)%n==0:
        Ms[n]=Msup(p,n,g); n*=2
    for n in sorted(Ms):
        if n//2 in Ms and Ms[n//2]>0:
            m=(p-1)//n; lnm=log(m); x=n/lnm; beta=log(p)/log(n)
            ratio=Ms[n]/Ms[n//2]
            rows.append((x,beta,ratio))
def corr(a,b):
    ma,mb=statistics.mean(a),statistics.mean(b)
    da=sqrt(sum((y-ma)**2 for y in a)); db=sqrt(sum((y-mb)**2 for y in b))
    return sum((y-ma)*(z-mb) for y,z in zip(a,b))/(da*db)
xs=[r[0] for r in rows]; bs=[r[1] for r in rows]; rs=[r[2] for r in rows]
lxs=[log(x) for x in xs]
print(f"N={len(rows)} samples")
print(f"corr(log x, ratio)   = {corr(lxs,rs):+.3f}  <- x=n/lnm should DRIVE ratio")
print(f"corr(beta,  ratio)   = {corr(bs,rs):+.3f}")
print(f"corr(log x, beta)    = {corr(lxs,bs):+.3f}")
# partial corr of beta,ratio controlling for log x
def partial(y,z,c):
    # residualize y and z on c
    rc=corr
    byc=corr(c,y); bzc=corr(c,z)
    # regression slopes
    mc=statistics.mean(c); my=statistics.mean(y); mz=statistics.mean(z)
    vc=sum((t-mc)**2 for t in c)
    sy=sum((t-mc)*(u-my) for t,u in zip(c,y))/vc
    sz=sum((t-mc)*(u-mz) for t,u in zip(c,z))/vc
    ry=[u-(my+sy*(t-mc)) for t,u in zip(c,y)]
    rz=[u-(mz+sz*(t-mc)) for t,u in zip(c,z)]
    return corr(ry,rz)
print(f"partial corr(beta, ratio | log x) = {partial(bs,rs,lxs):+.3f}  <- ~0 means beta irrelevant once x fixed")
print(f"partial corr(log x, ratio | beta) = {partial(lxs,rs,bs):+.3f}  <- strong means x is the true driver")
# CONTROL for x: within narrow x band, does beta move ratio?
print("\nWithin fixed x-band, vary beta:")
for lo,hi in [(1,2),(2,4),(4,8)]:
    sub=[r for r in rows if lo<=r[0]<hi]
    if len(sub)>=8:
        sb=[r[1] for r in sub]; sr=[r[2] for r in sub]
        print(f"  x in [{lo},{hi}): n={len(sub)} corr(beta,ratio)={corr(sb,sr):+.3f} ratio_range=[{min(sr):.3f},{max(sr):.3f}] beta_range=[{min(sb):.2f},{max(sb):.2f}]")
