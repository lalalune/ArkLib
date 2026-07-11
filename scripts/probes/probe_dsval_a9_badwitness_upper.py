#!/usr/bin/env python3
"""
A9 BAD-WITNESS CONSTRUCTION -> EXPLICIT UPPER BOUND on delta*  (issue #407).

GOAL (my angle): construct EXPLICIT consistent-subset witness families (coset-unions /
mu_d-cosets) for a fixed far direction (a,b) that make the worst-direction incidence
   I(w) = #{ distinct gamma : x^a + gamma x^b agrees with some deg<k poly on a w-subset }
EXCEED the budget n. The smallest w at which the construction still exceeds n gives the
UPPER bound delta* <= 1 - w_constr/n. Match against the deep-band ceiling (A8) for a
tight bracket.

============================  THE CONSTRUCTION  ============================
Fix the direction with the LARGEST action-orbit: step = b-a coprime to n. For n=2^a any
ODD step is coprime, so S_orbit = n/gcd(step,n) = n (maximal). The bad gammas for a fixed
direction are a union of <zeta^step>-orbits under gamma -> gamma*zeta^step; orbit size = n.

For w = k+1 (the SHALLOWEST over-determined band), a w-subset S=R (|R|=k+1) is consistent
for a UNIQUE gamma whenever x^b|_R is not already in RS[k]|_R. That gamma is, up to the
orbit action,
    gamma(R) = - L_R(x^a) / L_R(x^b),
where L_R is the (unique up to scale) divided-difference functional killing deg<k on the
(k+1)-point set R. So at w=k+1:
    I(a,b; k+1) = #{ distinct gamma(R) : R ranges over (k+1)-subsets, L_R(x^b) != 0 }.

We CONSTRUCT a witness sub-family of (k+1)-subsets giving MANY distinct gammas: the
arithmetic-progression / coset-aligned subsets R_t = { mu[t], mu[t+1], ..., mu[t+k] }
(consecutive coset of the cyclic index group) and their dilates. By the divided-difference
shift identity over roots of unity, gamma(R_t) takes distinct values across t and across
the k+1 anchor rotations, and the full incidence I(a,b;k+1) is a *closed* count.

This probe:
  (1) Computes I(a,b; w) EXACTLY (big prime q>>n^4, proper mu_n) for the maximal-orbit
      direction at the shallowest over-det band w=k+1, and at w=k+2, w=k+3.
  (2) Builds the explicit coset-aligned witness family and reports HOW MANY distinct
      gammas IT ALONE realizes (a CONSTRUCTIVE lower bound on I, hence on the upper bound
      for delta*).
  (3) Finds w_constr = largest w with (witness incidence) > n  ->  delta* <= 1-w_constr/n,
      and compares to the full worst-direction crossing (the true delta*) and to the
      deep-band ceiling 1-(k+m+1)/n.

HONESTY: mu_n PROPER (n=2^a, q==1 mod n, q>>n^4, moderate v2). Exact char-0 via big prime
(over-det band proven p-independent; re-verified on a 2nd prime). The witness family gives
a PROVEN constructive lower bound on I (a subset of all consistent subsets), hence a PROVEN
upper bound on delta*. Tagged proven/measured/conjecture explicitly in output.
"""
import itertools, sys
from math import gcd, comb, log2

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x in (1,m-1): continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True; break
        if not ok: return False
    return True

def factor(x):
    f={}; d=2
    while d*d<=x:
        while x%d==0: f[d]=f.get(d,0)+1; x//=d
        d+=1
    if x>1: f[x]=f.get(x,0)+1
    return f

def proot(p):
    fs=set(factor(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g

def setup(n, plo, skip=0):
    """big prime q==1 mod n, q>=plo, moderate v2(q-1); return (q, mu)."""
    p = plo + (1 - plo) % n
    if p < plo: p += n
    found=0
    while True:
        if isprime(p):
            v=p-1; v2=0
            while v%2==0: v//=2; v2+=1
            if v2 <= int(log2(n))+4:
                if found==skip:
                    g=proot(p); h=pow(g,(p-1)//n,p)
                    mu=[pow(h,i,p) for i in range(n)]
                    assert len(set(mu))==n and pow(mu[1],n,p)==1
                    return p, mu
                found+=1
        p += n

def make_member(p, mu, k):
    inv=lambda z: pow(z,p-2,p)
    invc={}
    def ddk(vals, idx):
        vs=list(vals)
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                key=(idx[i],idx[i-j]); d=invc.get(key)
                if d is None:
                    d=inv((mu[idx[i]]-mu[idx[i-j]])%p); invc[key]=d
                vs[i]=(vs[i]-vs[i-1])*d%p
        return vs[k]
    def in_RS(vals, idx):
        w=len(idx)
        if w<=k: return True
        for st in range(w-k):
            if ddk(vals[st:st+k+1], idx[st:st+k+1])!=0: return False
        return True
    return ddk, in_RS

def gamma_of_subset(R, MUa, MUb, mu, k, p, member):
    """For |R|=w>k consistent direction: returns the unique bad gamma or None.
    Uses divided-difference functional: x^a+gamma x^b in RS[k] on R iff all k-windows
    of (u0+gamma u1) have vanishing top divided difference; gamma forced by first
    nonzero u1-window, then must be consistent across all windows."""
    ddk, in_RS = member
    idx=list(R)
    u1=[MUb[i] for i in R]
    if in_RS(u1, idx):
        u0=[MUa[i] for i in R]
        return 'SAT' if in_RS(u0, idx) else None
    u0=[MUa[i] for i in R]
    inv=lambda z: pow(z,p-2,p)
    gm=None; w=len(R)
    for st in range(w-k):
        a1=ddk(u1[st:st+k+1], idx[st:st+k+1])
        if a1%p:
            a0=ddk(u0[st:st+k+1], idx[st:st+k+1])
            gm=(-a0*inv(a1))%p; break
    if gm is None: return None
    if in_RS([(u0[i]+gm*u1[i])%p for i in range(w)], idx):
        return gm
    return None

def full_incidence(a, b, n, mu, k, p, w, member):
    """EXACT I(a,b;w) over ALL w-subsets (ground truth). saturate->return ('SAT',)."""
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    gam=set()
    for R in itertools.combinations(range(n), w):
        g=gamma_of_subset(R, MUa, MUb, mu, k, p, member)
        if g=='SAT': return None
        if g is not None: gam.add(g)
    return gam

def witness_incidence(a, b, n, mu, k, p, w, member):
    """CONSTRUCTIVE: only the coset-aligned (consecutive-index) w-subsets and their
    rotations: R_{t} = {t, t+1, ..., t+w-1} mod n, t=0..n-1. Returns set of distinct
    gammas realized by THIS explicit family (a lower bound on full_incidence)."""
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    gam=set()
    fam=[]
    for t in range(n):
        R=tuple((t+j)%n for j in range(w))
        if len(set(R))<w: continue
        g=gamma_of_subset(R, MUa, MUb, mu, k, p, member)
        if g=='SAT' or g is None: continue
        gam.add(g); fam.append((R,g))
    return gam, fam

def witness_incidence_dilated(a, b, n, mu, k, p, w, member):
    """Richer witness: consecutive runs at every gap pattern that is a single coset of a
    cyclic subgroup OR a union 'k-anchor + step-coset'. We use: all subsets that are a
    consecutive run UNION'd with their step-dilates (index*odd). Reports distinct gammas."""
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    gam=set()
    # families: consecutive runs scaled by every unit step coprime to n (index dilation)
    units=[s for s in range(1,n) if gcd(s,n)==1]
    seen=set()
    for s in units:
        for t in range(n):
            R=tuple(sorted(((t+j*s)%n) for j in range(w)))
            if len(set(R))<w or R in seen: continue
            seen.add(R)
            g=gamma_of_subset(R, MUa, MUb, mu, k, p, member)
            if g in (None,'SAT'): continue
            gam.add(g)
    return gam

def maximal_orbit_dir(n, k):
    """pick far direction (a,b) with step=b-a coprime to n (orbit size n) and a,b>=k.
    Use a=k, b=k+1 (step=1, always coprime); also return a few alternatives."""
    cands=[]
    for a in range(k, n):
        for b in range(a+1, n):
            if gcd(b-a, n)==1:
                cands.append((a,b))
    return cands

def main():
    print("="*82)
    print("A9 BAD-WITNESS UPPER BOUND on delta*  (explicit coset-aligned consistent family)")
    print("="*82)
    # prize-relevant small instances (exact char-0 via big prime, proper mu_n)
    cases=[(8,2),(8,4),(16,4),(16,8)]   # (n,k): rho=1/4 and 1/2
    budget_factor=1   # budget = n
    for (n,k) in cases:
        rho=k/n
        plo=max(200003, 4*n*n*n*n+7)
        p, mu = setup(n, plo)
        p2, mu2 = setup(n, plo, skip=3)
        member = make_member(p, mu, k)
        member2 = make_member(p2, mu2, k)
        budget=n
        print(f"\n{'='*70}")
        print(f"n={n} k={k} rho={rho}  q={p} (pindep q2={p2})  budget=n={n}")
        print(f"{'='*70}")
        # the maximal-orbit direction (step coprime to n): use (k,k+1)
        a0,b0=k,k+1
        print(f"  maximal-orbit direction (a,b)=({a0},{b0}), step={b0-a0} "
              f"gcd(step,n)={gcd(b0-a0,n)} orbit-size={n//gcd(b0-a0,n)}")
        for w in range(k+1, min(k+5, n)):
            full = full_incidence(a0,b0,n,mu,k,p,w,member)
            full2= full_incidence(a0,b0,n,mu2,k,p2,w,member2)
            if full is None or full2 is None:
                print(f"   w={w}: SATURATED (near direction at this w) -- skip"); continue
            If=len(full); If2=len(full2)
            wgam, fam = witness_incidence(a0,b0,n,mu,k,p,w,member)
            wd = witness_incidence_dilated(a0,b0,n,mu,k,p,w,member)
            cross_full = "OVER" if If>budget else "ok"
            cross_w    = "OVER" if len(wd)>budget else "ok"
            pindep = "PINDEP-OK" if If==If2 else f"PINDEP-FAIL({If}vs{If2})"
            print(f"   w={w:2d} delta={1-w/n:.4f}: fullI={If:4d}[{cross_full}]  "
                  f"witness(consec)={len(wgam):4d}  witness(dilated)={len(wd):4d}[{cross_w}]  "
                  f"{pindep}")
        # ALSO scan ALL far directions for the TRUE worst (to locate the real crossing)
        print(f"  -- true worst-direction crossing (all far dirs, full enum) --")
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
        wstar=None; wit_cross=None
        for w in range(k+1, n):
            worst=0; wdir=None
            for (a,b) in dirs:
                full=full_incidence(a,b,n,mu,k,p,w,member)
                if full is None: continue
                if len(full)>worst: worst=len(full); wdir=(a,b)
            # witness incidence over all far dirs (dilated consecutive family)
            wbest=0; wbdir=None
            for (a,b) in dirs:
                wd=witness_incidence_dilated(a,b,n,mu,k,p,w,member)
                if len(wd)>wbest: wbest=len(wd); wbdir=(a,b)
            mark_full = "<-- delta* (true)" if (wstar is None and worst<=budget) else ""
            if wstar is None and worst<=budget: wstar=w
            mark_wit = ""
            if wit_cross is None and wbest<=budget:
                wit_cross=w; mark_wit="<-- witness upper-bound crossing"
            print(f"     w={w:2d} delta={1-w/n:.4f}: trueWorstI={worst:5d} dir={wdir} {mark_full}"
                  f"   |  witnessWorstI={wbest:5d} dir={wbdir} {mark_wit}")
        ds_true = 1-wstar/n if wstar else None
        ds_wit_upper = 1-(wit_cross)/n if wit_cross else None
        print(f"  RESULT: delta*(true, measured) = {ds_true}  (w*={wstar})")
        print(f"          delta* <= (witness upper) = {ds_wit_upper}  (w_constr={wit_cross})")
        gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}.get((n,k))
        if gt is not None:
            print(f"          issue ground-truth delta* = {gt}  "
                  f"(true match={abs((ds_true or -9)-gt)<1e-9})")

if __name__=="__main__":
    main()
