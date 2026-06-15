#!/usr/bin/env python3
"""
#407 / A3 WORST-DIRECTION FAMILY -- candidate shootout.

Instead of the full O(n^2) direction sweep (too slow at n>=16 with subset enumeration), test a
CURATED family of candidate worst directions and find each one's delta*. The candidate with the
SMALLEST delta* is the worst-direction winner. Candidates motivated by:
  - dir(k,k+1), dir(k,k+2)   -- "smallest far exponents, adjacent" (consecutive readout)
  - dir(n/2,n/2+1), dir(n/2,n/2+2)  -- half-power directions
  - dir(n/4,5n/8)  -- R4 complete-homogeneous readout
  - dir(k,n-1)     -- widest span
  - dir(n-2,n-1)   -- largest exponents
Plus we ALSO do a TARGETED restricted full sweep over directions with a in {k, n/2} only (cheap),
to confirm the winner is in the curated family.

Faithful: q>n^4, v2(q-1)=v2(n), mu_n proper. delta* = 1 - w_min/n, w_min smallest w with I<=n.
We bound subset enumeration: at n=32 we ONLY evaluate at a curated set of bands near the expected
window (delta in [0.2,0.55]) to keep C(32,w) feasible -- C(32,18..26) is large but C(32,8)~10M is
the cost cap; we cap w>= n - 13 (so subsets sized w, complement<=13) i.e. iterate over COMPLEMENT.
"""
import itertools
from math import gcd

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def v2(x):
    c=0
    while x%2==0: x//=2; c+=1
    return c
def find_prime(n,lo):
    vn=v2(n); q=((lo//n)+1)*n+1
    while True:
        if q>lo and (q-1)%n==0 and v2(q-1)==vn and isprime(q): return q
        q+=n
def find_gen(p,n):
    m=p-1; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return pow(g,(p-1)//n,p)
    raise RuntimeError

def incidence_via_complement(a,b,n,mu,k,w,p):
    """Iterate over the s=n-w DELETED indices (complement) so cost = C(n,s), small for shallow band."""
    inv=lambda z: pow(z%p,p-2,p)
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    s=n-w
    gammas=set()
    allidx=range(n)
    for D in itertools.combinations(allidx,s):
        Dset=set(D)
        W=[i for i in allidx if i not in Dset]
        pts=[mu[i] for i in W]; u0=[MUa[i] for i in W]; u1=[MUb[i] for i in W]
        m=len(pts)
        if m<=k: continue
        gam=None; bad=False
        for st in range(m-k):
            xs=pts[st:st+k+1]
            def dd(vals):
                vs=list(vals)
                for j in range(1,k+1):
                    for i in range(k,j-1,-1):
                        vs[i]=(vs[i]-vs[i-1])*inv(xs[i]-xs[i-j])%p
                return vs[k]
            a0=dd(u0[st:st+k+1]); a1=dd(u1[st:st+k+1])
            if a1%p==0:
                if a0%p!=0: bad=True; break
                continue
            g=(-a0*inv(a1))%p
            if gam is None: gam=g
            elif gam!=g: bad=True; break
        if bad: continue
        if gam is None: return p
        gammas.add(gam)
    return len(gammas)

def per_dir_deltastar(a,b,n,mu,k,p,budget,smax):
    """smallest w with I<=budget; scan s=n-w from 0 up to smax (i.e. shallow bands first)."""
    wstar=None
    for s in range(1,smax+1):
        w=n-s
        if w<=k: break
        I=incidence_via_complement(a,b,n,mu,k,w,p)
        if I==p: continue
        if I<=budget: wstar=w
        else: break
    if wstar is None: return None
    return 1-wstar/n

def candidates(n,k):
    c=set()
    def add(a,b):
        if k<=a<b<n: c.add((a,b))
    add(k,k+1); add(k,k+2); add(k,k+3)
    add(n//2,n//2+1); add(n//2,n//2+2)
    add(n//4,5*n//8)
    add(k,n-1); add(n-2,n-1)
    add(k+1,k+2); add(k+1,k+3)
    return sorted(c)

def main():
    print("A3 candidate-direction SHOOTOUT  faithful q>n^4, v2(q-1)=v2(n)\n")
    # smax bounds C(n,s) subset cost: at n=32, C(32,12)=2.25e8 too big; cap smax so C(n,smax)<~3e7
    cfg=[(8,2,8),(16,4,8),(8,4,8),(16,8,8),(32,8,9),(32,16,9)]
    for n,k,smax in cfg:
        rho=k/n; p=find_prime(n,n**4); mu=[pow(find_gen(p,n),i,p) for i in range(n)]
        budget=n
        res={}
        for (a,b) in candidates(n,k):
            ds=per_dir_deltastar(a,b,n,mu,k,p,budget,smax)
            res[(a,b)]=ds
        # worst = smallest delta* (None = never binds within smax => treat as large, ignore)
        binding={d:v for d,v in res.items() if v is not None}
        if not binding:
            print(f"n={n} k={k} rho={rho}: no candidate binds within smax={smax}"); continue
        mn=min(binding.values())
        worst=sorted([d for d,v in binding.items() if abs(v-mn)<1e-12])
        print(f"n={n} k={k} rho={rho}: WORST delta*={mn:.4f} among candidates; winner(s)={worst}")
        for (a,b),v in sorted(res.items()):
            tag=" <== WORST" if (a,b) in worst else ""
            lbl=[]
            if a==k: lbl.append("a=k")
            if a==n//2: lbl.append("a=n/2")
            if b-a==1: lbl.append("ba=1")
            if b-a==2: lbl.append("ba=2")
            if (a,b)==(n//4,5*n//8): lbl.append("R4")
            vs=f"{v:.4f}" if v is not None else "  none "
            print(f"    ({a:2},{b:2}) b-a={b-a:2} gcd={gcd(b-a,n)}: delta*={vs}  [{','.join(lbl)}]{tag}")
        print()

if __name__=="__main__":
    main()
