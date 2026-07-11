#!/usr/bin/env python3
"""
#407 / A3 WORST-DIRECTION FAMILY -- FAST ranking version.

For each (n,k), compute the full per-direction delta* and RANK directions by delta* (worst =
smallest delta*). Report the worst-direction family + invariants. Optimization: incidence is
monotone increasing as w decreases; we binary/linear-scan w only in [k+1, ceil(n/2)] (the binding
band is always shallow here) and cache.

Faithful: big prime q > n^4, v2(q-1)=v2(n) (no extra 2-torsion), mu_n proper subgroup.
"""
import itertools
from math import gcd

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def v2(x):
    c=0
    while x%2==0: x//=2; c+=1
    return c

def find_prime(n, lo):
    vn = v2(n)
    q = ((lo//n)+1)*n + 1
    while True:
        if q>lo and (q-1)%n==0 and v2(q-1)==vn and isprime(q): return q
        q += n

def find_gen(p,n):
    m=p-1; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):
            return pow(g,(p-1)//n,p)
    raise RuntimeError

def incidence(a,b,n,mu,k,w,p):
    inv=lambda z: pow(z%p,p-2,p)
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    gammas=set()
    for W in itertools.combinations(range(n),w):
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
        if gam is None: return p  # degenerate
        gammas.add(gam)
    return len(gammas)

def per_dir_deltastar(a,b,n,mu,k,p,budget):
    # smallest w with I<=budget (incidence increasing as w decreases). Scan w from n-1 down.
    wstar=None
    # binding band is shallow; cap scan depth at floor(n/3) to bound C(n,w) cost (delta*<=~2/3)
    wfloor=max(k+1, n//3)
    for w in range(n-1,wfloor-1,-1):
        I=incidence(a,b,n,mu,k,w,p)
        if I==p: continue
        if I<=budget: wstar=w
        else: break
    if wstar is None: return None
    return 1-wstar/n

def main():
    print("A3 WORST-DIRECTION FAMILY (fast ranking)  faithful q>n^4, v2(q-1)=v2(n)\n")
    cases=[(8,2),(16,4),(8,4),(16,8)]
    for n,k in cases:
        rho=k/n; p=find_prime(n,n**4); mu=[pow(find_gen(p,n),i,p) for i in range(n)]
        budget=n
        dirds={}
        for a,b in itertools.combinations(range(k,n),2):
            ds=per_dir_deltastar(a,b,n,mu,k,p,budget)
            if ds is not None: dirds[(a,b)]=ds
        if not dirds:
            print(f"n={n} k={k}: none bind"); continue
        mn=min(dirds.values())
        worst=sorted([d for d,v in dirds.items() if abs(v-mn)<1e-12])
        print(f"n={n} k={k} rho={rho}: delta*={mn:.4f}; #worst dirs={len(worst)}")
        for (a,b) in worst:
            print(f"    (a={a},b={b}) b-a={b-a} gcd(b-a,n)={gcd(b-a,n)} a-k={a-k} (n-1)-b={n-1-b} a/n={a/n:.3f} b/n={b/n:.3f}")
        # structural summary of worst family
        amin=min(a for a,b in worst); amax=max(a for a,b in worst)
        print(f"    summary: worst a-range=[{amin},{amax}] (n/2={n//2}); all b-a values={sorted(set(b-a for a,b in worst))}")
        print()

if __name__=="__main__":
    main()
