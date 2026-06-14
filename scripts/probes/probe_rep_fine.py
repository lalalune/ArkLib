#!/usr/bin/env python3
"""Locate δ*(repetition code) precisely vs Johnson. Exact ε_mca, finer δ grid, small p (n-k=n-1
makes it costly so keep p,n modest). Repetition code C={(c,...,c)}."""
import itertools, math
def epsmca_rep(p,n,num):
    delta=num/n; smin=math.ceil((1-delta)*n)
    Ss=[frozenset(s) for r in range(smin,n+1) for s in itertools.combinations(range(n),r)]
    def ext(w,S):
        v={w[j] for j in S}; return len(v)<=1
    best=0
    for tail0 in itertools.product(range(p),repeat=n-1):
        u0=(0,)+tail0
        e0={S:ext(u0,S) for S in Ss}
        for tail1 in itertools.product(range(p),repeat=n-1):
            u1=(0,)+tail1
            e1={S:ext(u1,S) for S in Ss}
            joint={S:(e0[S] and e1[S]) for S in Ss}
            cnt=0
            for g in range(p):
                lp=tuple((u0[j]+g*u1[j])%p for j in range(n))
                if any(ext(lp,S) and not joint[S] for S in Ss): cnt+=1
            if cnt>best: best=cnt
    return best
for (p,n) in [(3,6),(5,5),(3,5)]:
    rho=1/n; J=1-math.sqrt(rho); cap=1-rho
    jn=J*n
    print(f"p={p} n={n} k=1 rho=1/{n} Johnson={J:.4f}(={jn:.3f}/{n}) cap={cap:.3f}")
    prev=None
    for num in range(1,n):
        bc=epsmca_rep(p,n,num); d=num/n
        mark="  <-- JUMP" if (prev is not None and bc>prev) else ""
        reg="below-J" if d<J else ("interior" if d<cap else "≥cap")
        print(f"   δ={num}/{n}={d:.3f} [{reg:8s}]: ε_mca={bc}/{p}={bc/p:.3f}{mark}")
        prev=bc
