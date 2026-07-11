#!/usr/bin/env python3
"""
#407 / A3 -- confirm worst-direction FAMILY a=n/2 (b-a in {1,2}) at larger n (n=32, n=64),
and pin delta*(n,rho) closed form.

We ONLY test the identified worst family + controls (a=k, R4) -> few directions -> feasible.
Cost is C(n,s) for shallow bands; we scan s upward from 1 until incidence exceeds budget.

Faithful: q>n^4, v2(q-1)=v2(n), mu_n proper subgroup.
"""
import itertools
from math import gcd, log2

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

def incidence_complement(a,b,n,mu,k,s,p):
    """incidence at w=n-s, iterating over s deleted indices. Returns count or -1 if degenerate."""
    inv=lambda z: pow(z%p,p-2,p)
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    gammas=set()
    for D in itertools.combinations(range(n),s):
        Ds=set(D); W=[i for i in range(n) if i not in Ds]
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
        if gam is None: return -1
        gammas.add(gam)
    return len(gammas)

def deltastar_dir(a,b,n,mu,k,p,budget,smax):
    """smallest w with I<=budget = largest s with I<=budget (scan s up, stop when I>budget)."""
    wstar=None
    for s in range(1,smax+1):
        w=n-s
        if w<=k: break
        I=incidence_complement(a,b,n,mu,k,s,p)
        if I==-1: continue  # degenerate band, treat as <=budget (line fully agrees)
        if I<=budget: wstar=w
        else: break
    if wstar is None: return None
    return 1-wstar/n

def main():
    print("A3 worst-FAMILY confirmation at large n  faithful q>n^4, v2(q-1)=v2(n)\n")
    # (n,k,smax) -- smax caps C(n,smax). n=32: C(32,8)=10.5M ok, C(32,9)=28M slow. cap 8.
    # n=64: C(64,5)=7.6M ok, C(64,6)=74M too slow -> cap 6 maybe. We aim to capture binding s.
    cfg=[(32,8,8),(32,16,8),(64,16,6),(64,32,6)]
    for n,k,smax in cfg:
        rho=k/n; p=find_prime(n,n**4); mu=[pow(find_gen(p,n),i,p) for i in range(n)]
        budget=n
        dirs=[(k,k+1,'a=k'),(k,k+2,'a=k,b-a=2'),
              (n//2,n//2+1,'a=n/2'),(n//2,n//2+2,'a=n/2,b-a=2'),
              (n//4,5*n//8,'R4')]
        print(f"n={n} k={k} rho={rho} p={p}  (smax={smax}, so deepest detectable delta={smax/n:.3f})")
        results={}
        for a,b,lbl in dirs:
            if not (k<=a<b<n): continue
            ds=deltastar_dir(a,b,n,mu,k,p,budget,smax)
            results[(a,b,lbl)]=ds
            dss=f"{ds:.4f}" if ds is not None else ">"+f"{(1-(n-smax)/n):.4f}(capped)"
            print(f"    ({a:2},{b:2}) [{lbl:11}] b-a={b-a:2} gcd={gcd(b-a,n)}: delta*={dss}")
        binders={k2:v for k2,v in results.items() if v is not None}
        if binders:
            mn=min(binders.values())
            w=[k2 for k2,v in binders.items() if abs(v-mn)<1e-12]
            print(f"    => WORST among tested = {mn:.4f} at {[(a,b) for a,b,l in w]}")
            print(f"       (1-rho)-delta*={(1-rho)-mn:.4f}; [(1-rho)-delta*]*log2(n)={((1-rho)-mn)*log2(n):.4f}")
        print()

if __name__=="__main__":
    main()
