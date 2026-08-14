import itertools, sys
# Over-determined incidence MAX as function of n (k=2, s=k+2=4, over-det s-k=2), char-0 (one big prime).
# Goal: confirm the cubic sequence 9,37,97,201,361,589 (n=8,12,16,20,24,28) and DERIVE the closed form.
# Also report (a) the extremal direction, (b) value at claimed extremal (n/2, n/2-1).
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
    # large prime p == 1 mod n, p >> n^3 (char-0 regime). take p ~ around 1_000_000+ but >= n^4 safety
    import math
    base = max(1000003, n**4)
    c = base + ((1 - base) % n)
    while not isprime(c): c += n
    return c
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
def maxinc(n,k=2):
    s=k+2; r=n-s; p=find_prime(n); mu=setup(n,p)
    best=0;arg=None
    extremal_dir=(n//2, n//2-1)
    extremal_val=None
    for a in range(k,n):
        for b in range(k,n):
            if a==b:continue
            I=incidence(a,b,n,mu,k,p,r)
            if I<p:
                if I>best:best=I;arg=(a,b)
                if (a,b)==extremal_dir: extremal_val=I
    return best,arg,extremal_val,p
seq=[]
for n in [8,12,16,20,24,28]:
    best,arg,exv,p=maxinc(n)
    seq.append(best)
    print(f"n={n}: MAX={best} at {arg}; val@(n/2,n/2-1)={exv}; p={p}",flush=True)
print("SEQ:",seq,flush=True)
# second differences
d1=[seq[i+1]-seq[i] for i in range(len(seq)-1)]
d2=[d1[i+1]-d1[i] for i in range(len(d1)-1)]
print("1st diffs:",d1,flush=True)
print("2nd diffs:",d2,flush=True)
# fit cubic in n via sympy on the n-grid {8,12,16,20,24,28}
import sympy as sp
ns=[8,12,16,20,24,28]
x=sp.symbols('x')
poly=sp.interpolate(list(zip(ns,seq)),x)
print("interp poly in n:",sp.expand(poly),flush=True)
print("DONE")
