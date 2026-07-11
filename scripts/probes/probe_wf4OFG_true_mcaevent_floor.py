"""
wf-OFG (#444): TRUE mcaEvent bad-γ count (WITH the no-joint-agreement clause) at δbind.

epsMCA(C,δ) = (1/q) max_{u0,u1} #{γ : EXISTS s*-set S with
   (line u0+γ u1 = some codeword on S) AND (no codeword PAIR (v0,v1) agrees with (u0,u1) on S)}.

The previous probe counted line-explainability only (the FAR over-approx). Here we also
test the joint-agreement clause, so near-code directions are correctly DEFLATED. This decides
whether the near/under-det stratum contributes to the floor at δbind, i.e. whether
`epsMCA(C,δbind) <= eps*` is reachable from the over-det (far) count alone.

Char-0: p == 1 mod n, p > n^4. ρ=1/4, k=n/4, s* = n/2-1 (agreement size), δbind=(n-s*)/n.
Budget ~ n.
"""
import itertools, sys
from collections import Counter

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
def find_prime(n,lo):
    p=lo-lo%n+1
    while True:
        if p>lo and isprime(p):return p
        p+=n
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

def mcaevent_count(u0,u1,mu,n,k,p,sset_size):
    """TRUE #{γ : mcaEvent}. For each γ, check EXISTS S (size sset_size) with line
    on S in RS[k] AND (u0,u1) not jointly explainable on S."""
    inv=lambda z:pow(z,p-2,p)
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
    subsets=list(itertools.combinations(range(n),sset_size))
    # precompute per-subset: is u0 in RS, is u1 in RS, the forced γ (if u1 not in RS)
    bad=set()
    for R in subsets:
        pts=[mu[i] for i in R]; a0=[u0[i] for i in R]; a1=[u1[i] for i in R]
        u0R=in_RS(a0,pts); u1R=in_RS(a1,pts)
        # joint-agreement on S: exists codeword pair (v0,v1) agreeing with (u0,u1) on S
        # <=> u0|S in RS[k]  AND  u1|S in RS[k]  (independent interpolation on s*>=k+1 pts)
        joint = u0R and u1R
        if joint: continue   # mcaEvent's no-joint clause fails => not bad via this S
        if u1R:
            # u1|S in RS but u0|S not => line in RS for NO γ (would need u0 in RS). skip
            continue
        d0=ddk(a0,pts); d1=ddk(a1,pts)
        if d1%p==0: continue
        gm=(-d0*inv(d1))%p
        lineR=in_RS([(a0[i]+gm*a1[i])%p for i in range(sset_size)],pts)
        if lineR:
            bad.add(gm)   # γ=gm is mcaEvent-bad witnessed by S (joint clause holds: not both in RS)
    return len(bad)

def run(n):
    p=find_prime(n,n**4*4); mu=setup(n,p)
    k=n//4; sstar=n//2-1; sset=sstar   # agreement/witness size = s*
    budget=n
    print(f"=== n={n} p={p} k={k} s*(agree size)={sstar} δbind={(n-sstar)}/{n}={(n-sstar)/n:.4f} budget~n={budget}",flush=True)
    best=0;arg=None;dist=Counter()
    # monomials
    for a in range(n):
        for b in range(n):
            if a==b:continue
            u0=[pow(x,a,p) for x in mu]; u1=[pow(x,b,p) for x in mu]
            c=mcaevent_count(u0,u1,mu,n,k,p,sset)
            dist[c]+=1
            if c>best:best=c;arg=("mono",a,b)
    # 2-term near/far directions
    for b in range(n):
        for bp in range(n):
            if b==bp:continue
            for cf in (1,2,p-1):
                u1=[(pow(x,b,p)+cf*pow(x,bp,p))%p for x in mu]
                u0=[pow(x,(b+1)%n,p) for x in mu]
                c=mcaevent_count(u0,u1,mu,n,k,p,sset)
                dist[c]+=1
                if c>best:best=c;arg=("2term",b,bp,cf)
    print(f"  MAX true-mcaEvent bad-γ count = {best} at {arg}",flush=True)
    print(f"  => epsMCA(δbind)<=eps* {'HOLDS on family' if best<=budget else 'FAILS on family'} (max={best} vs budget={budget})",flush=True)
    print(f"  top dist: {dict(sorted(dist.items())[-6:])}",flush=True)

if __name__=="__main__":
    for n in (8,16):
        run(n)
    print("DONE",flush=True)
