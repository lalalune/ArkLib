import itertools
def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
        if a%x==0:continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f={};dd=2
    while dd*dd<=x:
        while x%dd==0:f[dd]=f.get(dd,0)+1;x//=dd
        dd+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def setup(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p);return [pow(h,i,p) for i in range(n)]
def incidence(a,b,n,mu,k,p,r):
    s=n-r;gam=set();inv=lambda z:pow(z,p-2,p)
    MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
    def ddk(vals,pts):
        vs=list(vals[:k+1]);xs=pts[:k+1]
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*inv((xs[i]-xs[i-j])%p)%p
        return vs[k]
    def in_RS(vals,pts):
        if len(pts)<=k:return True
        for st in range(len(pts)-k):
            if ddk(vals[st:st+k+1],pts[st:st+k+1])!=0:return False
        return True
    for R in itertools.combinations(range(n),s):
        pts=[mu[i] for i in R];u0=[MUa[i] for i in R];u1=[MUb[i] for i in R]
        if in_RS(u1,pts):
            if in_RS(u0,pts):return p
            continue
        a0=ddk(u0,pts);a1=ddk(u1,pts)
        if a1%p==0:continue
        gm=(-a0*inv(a1))%p
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(s)],pts):gam.add(gm)
    return len(gam)
n=32;k=2;s=4;r=n-s
dirs=[(a,b) for b in range(k,s) for a in range(k,n) if a!=b]  # far: b in {2,3}
print(f"n={n} k={k} s={s}: MAX over {len(dirs)} VALID FAR dirs (b<{s}), 4 primes incl prize-scale 1048609",flush=True)
res={}
for p in [97, 1153, 3137, 1048609]:
    mu=setup(n,p);mx=0;arg=None
    for (a,b) in dirs:
        I=incidence(a,b,n,mu,k,p,r)
        if I<p and I>mx: mx=I;arg=(a,b)
    res[p]=(mx,arg)
    print(f"  p={p:>9}: maxI={mx} at {arg}",flush=True)
uniq=set(v[0] for v in res.values())
print(f"\ndistinct maxI = {uniq} => {'p-INDEPENDENT over valid far dirs (incl prize-scale!)' if len(uniq)==1 else 'p-DEPENDENT'}",flush=True)
print("DONE")
