#!/usr/bin/env python3
"""r=2 KKH26-family endpoint: the DIMENSION-1 (constant) code C={(c,...,c)}. Exact ε_mca curve.
mcaEvent at radius δ: line point u0+γu1 is δ-close to a constant (some value repeated ≥(1-δ)n times)
but the pair (u0,u1) is NOT jointly close (both u0,u1 close to constants on the same witness set).
Question: is ε_mca good-below some radius then jumps? i.e. is δ* pinnable for the constant code?"""
import itertools, math
def naive_epsmca_const(p,n,num):
    delta=num/n; smin=math.ceil((1-delta)*n)
    C=[tuple([c]*n) for c in range(p)]  # constant codewords
    Ss=[frozenset(s) for r in range(smin,n+1) for s in itertools.combinations(range(n),r)]
    def ext(w,S):  # some constant agrees with w on all of S  <=> w is constant on S
        vals={w[j] for j in S}; return len(vals)<=1
    best=0; argbest=None
    # syndrome reduction: codewords are constants; transversal = words with w[0]=0 (subtract const)
    for tail0 in itertools.product(range(p),repeat=n-1):
        u0=(0,)+tail0
        for tail1 in itertools.product(range(p),repeat=n-1):
            u1=(0,)+tail1
            e0={S:ext(u0,S) for S in Ss}; e1={S:ext(u1,S) for S in Ss}
            joint={S:(e0[S] and e1[S]) for S in Ss}
            cnt=0
            for g in range(p):
                lp=tuple((u0[j]+g*u1[j])%p for j in range(n))
                if any(ext(lp,S) and not joint[S] for S in Ss): cnt+=1
            if cnt>best: best=cnt; argbest=(u0,u1)
    return best,argbest
for (p,n) in [(7,3),(5,4),(7,4)]:
    rho=1/n; J=1-math.sqrt(rho); cap=1-rho
    print(f"p={p} n={n} k=1 rho=1/{n}  Johnson={J:.3f} cap={cap:.3f}")
    for num in range(1,n):
        bc,arg=naive_epsmca_const(p,n,num)
        d=num/n; reg = "below-J" if d<J else ("interior" if d<cap else "≥cap")
        print(f"   δ={num}/{n}={d:.3f} [{reg}]: ε_mca={bc}/{p}={bc/p:.3f}")
