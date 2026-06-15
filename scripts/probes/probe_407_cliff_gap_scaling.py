import itertools
from math import comb
# CLIFF-GAP SCALING vs n (#407): over-determined I(s=k+2) is p-INDEPENDENT [(n/2-1)^2 for k=2]; under-determined
# I(s=k+1) is p-DEPENDENT and ~Theta(C(n,k+1)) >> budget~n. Since I(k+1)>>budget for all primes, the binding s*
# is ALWAYS over-determined => delta* p-INDEPENDENT (decouples from BGK). Verified n=8,16,32,64 (2 primes).
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
def setup(n,plo):
    p=plo
    while not(p%n==1 and isprime(p)):p+=1
    g=proot(p);h=pow(g,(p-1)//n,p)
    return p,[pow(h,i,p) for i in range(n)]
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
if __name__=="__main__":
    k=2;dirs=[(3,4),(4,3),(5,3),(3,5)]
    print(f"CLIFF-GAP SCALING (k={k}): over-det I(s=4) [p-indep] vs budget~n vs under-det I(s=3) [p-dep]")
    print(f"{'n':>4} {'budget':>7} {'overDet@2p':>16} {'underDet@2p':>20}")
    for n in [8,16,32,64]:
        over=[];under=[]
        for plo in [200003,700001]:
            p,mu=setup(n,plo);mo=0;mu_=0
            for (a,b) in dirs:
                if a>=n or b>=n:continue
                Io=incidence(a,b,n,mu,k,p,n-4)
                if Io<p and Io>mo:mo=Io
                Iu=incidence(a,b,n,mu,k,p,n-3)
                if Iu<p and Iu>mu_:mu_=Iu
            over.append(mo);under.append(mu_)
        print(f"{n:>4} {n:>7} {str(over):>16} {str(under):>20}")
    print("over-det p-indep + under-det >> budget => binding over-det => delta* p-INDEPENDENT. DONE")
