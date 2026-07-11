import itertools
# FOCUSED s* finder: sweep s upward from k+2, BREAK at first s with maxI<=budget. Only the low over-det band.
# Restrict directions to antipodal neighborhood (proven extremal) to cut cost. Cross-check full at small n.
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
    base=max(1000003,n**4); c=base+((1-base)%n)
    while not isprime(c): c+=n
    return c
def setup(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p);return [pow(h,i,p) for i in range(n)]
def incidence_dir(a,b,n,mu,k,p,s):
    gam=set();inv=lambda z:pow(z,p-2,p)
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
def maxI(n,k,s,mu,p,full=False):
    h=n//2
    if full:
        dirs=[(a,b) for a in range(k,n) for b in range(k,n) if a!=b]
    else:
        dirs=[(a,b) for a in [h,h-1,h-2,h+1] for b in [h,h-1,h-2,h+1] if a!=b and a>=k and b>=k and 0<=a<n and 0<=b<n]
    best=0
    for (a,b) in dirs:
        I=incidence_dir(a,b,n,mu,k,p,s)
        if I<p and I>best: best=I
    return best
print("n  k | s* (first over-det s with maxI<=budget=n) | maxI(s*-1) maxI(s*) | s*-k | delta*=(n-s*)/n",flush=True)
for (n,k,full) in [(16,2,False),(16,4,False),(20,2,False),(20,4,False),(24,2,False),(24,4,False),(32,2,False)]:
    p=find_prime(n); mu=setup(n,p); budget=n
    prev=None; sstar=None
    for s in range(k+2, n):
        mI=maxI(n,k,s,mu,p,full=full)
        if mI<=budget:
            sstar=s; cur=mI; break
        prev=mI
    if sstar is not None:
        ds=(n-sstar)/n
        print(f"{n:3d} {k} | s*={sstar:2d} | prev={prev} cur={cur} | s*-k={sstar-k} | delta*={ds:.4f}{'  [full]' if full else '  [antip-nbhd]'}",flush=True)
    else:
        print(f"{n:3d} {k} | no s* found in over-det band",flush=True)
print("DONE")
