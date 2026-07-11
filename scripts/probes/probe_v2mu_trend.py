import math
# Trend of the BEST stratum (v2(p-1) = mu, minimal = generic prize prime): does c=M/sqrt(n ln m)
# stay below the envelope-break threshold 1.243 as n grows, or rise toward the saddle wall sqrt2=1.414?
def isprime(z):
    if z<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if z%q==0:return z==q
    d=z-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,z)
        if x in(1,z-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%z
            if x==z-1:ok=True;break
        if not ok:return False
    return True
def v2(z):
    c=0
    while z%2==0:z//=2;c+=1
    return c
def prroot(p):
    f=[];m=p-1;dd=2
    while dd*dd<=m:
        if m%dd==0:
            f.append(dd)
            while m%dd==0:m//=dd
        dd+=1
    if m>1:f.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//x,p)!=1 for x in f):return g
def Mexact(n,p):
    g=prroot(p);zeta=pow(g,(p-1)//n,p)
    D=[pow(zeta,i,p) for i in range(n)]
    m=(p-1)//n;tp=2*math.pi/p;best=0.0;gj=1
    for j in range(m):
        re=im=0.0
        for x in D:
            ang=((gj*x)%p)*tp; re+=math.cos(ang); im+=math.sin(ang)
        mag=math.hypot(re,im)
        if mag>best:best=mag
        gj=(gj*g)%p
    return best,m
print("v2=mu (minimal) stratum trend.  threshold(envelope)=1.243, saddle-wall sqrt2=1.4142")
print(f"{'n':>5} {'mu':>3} {'#primes':>7} {'max c':>8} {'mean c':>8} {'min c':>8}")
for mu in [3,4,5,6,7]:
    n=2**mu; lo=n**4; p=lo|1; cs=[]; hi=lo+8*(n**4)
    while p<hi and len(cs)<12:
        if (p-1)%n==0 and isprime(p) and v2(p-1)==mu:
            M,m=Mexact(n,p); cs.append(M/math.sqrt(n*math.log(m)))
        p+=2
    if cs:
        print(f"{n:>5} {mu:>3} {len(cs):>7} {max(cs):>8.4f} {sum(cs)/len(cs):>8.4f} {min(cs):>8.4f}",flush=True)
print("DONE")
