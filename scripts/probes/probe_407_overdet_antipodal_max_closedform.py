import itertools, sys
# FAST: over-det incidence at the EXTREMAL antipodal direction (a,b)=(n/2-1, n/2) ONLY (skip full sweep).
# Confirms I_max(n) = n^3/32 - n^2/8 + 1 = 2m^3-2m^2+1 (m=n/4) to large n, char-0.
def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
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
def find_prime(n):
    base = max(1000003, n**4)
    c = base + ((1 - base) % n)
    while not isprime(c): c += n
    return c
def setup(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p);return [pow(h,i,p) for i in range(n)]
def incidence_dir(a,b,n,mu,k,p,r):
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
k=2; s=4
print("n  | I(antipodal) | formula n^3/32-n^2/8+1 | match",flush=True)
for n in [8,12,16,20,24,28,32,36,40]:
    r=n-s; p=find_prime(n); mu=setup(n,p)
    a=n//2-1; b=n//2
    I=incidence_dir(a,b,n,mu,k,p,r)
    f=n**3//32 - n**2//8 + 1
    print(f"{n:3d}| {I:6d}       | {f:6d}                 | {I==f}",flush=True)
print("DONE")
