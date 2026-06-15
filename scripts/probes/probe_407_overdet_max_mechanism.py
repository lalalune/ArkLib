import itertools
# Decompose the I_max(n)=2m^3-2m^2+1 count at extremal dir (h,h-1), h=n/2, m=n/4.
# For each contributing gamma, record the witness sets R (size s=4) that produced it, to see structure.
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
def analyze(n,k=2):
    s=4; r=n-s; p=find_prime(n); mu=setup(n,p)
    h=n//2; a=h; b=h-1
    inv=lambda z:pow(z,p-2,p)
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
    gam={}
    for R in itertools.combinations(range(n),s):
        pts=[mu[i] for i in R];u0=[MUa[i] for i in R];u1=[MUb[i] for i in R]
        if in_RS(u1,pts):
            continue
        a0=ddk(u0,pts);a1=ddk(u1,pts)
        if a1%p==0:continue
        gm=(-a0*inv(a1))%p
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(s)],pts):
            gam.setdefault(gm,[]).append(R)
    # classify gamma: 0, +-1, antipodal-symmetric vs generic. count
    cnt=len(gam)
    f=2*(n//4)**3-2*(n//4)**2+1
    # how many gamma have an antipodal-symmetric witness (R closed under i->i+h mod n)?
    def antip(R): return all(((i+h)%n) in R for i in R)
    nsym=sum(1 for g,Rs in gam.items() if any(antip(R) for R in Rs))
    print(f"n={n} m={n//4}: #gamma={cnt} (formula {f}, match={cnt==f}); gamma w/ antipodal-closed witness={nsym}",flush=True)
    # gamma value histogram of small reps
    specials={g for g in gam if g in (0,1,p-1)}
    print(f"    special gammas present (0,+-1): {sorted(0 if x==0 else (1 if x==1 else -1) for x in specials)}",flush=True)
    return cnt,f
for n in [8,12,16,20,24]:
    analyze(n)
print("DONE")
