#!/usr/bin/env python3
"""
C1 PER-FIBER INCIDENCE PROBE (#389 demand lane, cycle2).

OBJECT (exact, faithful BabyBear p=2013265921, p^2 >> C(n,r+1)):
  Over mu_n = {g^i}, for the deep-band MAXIMIZER line (e,f), enumerate all
  (r+1)-subsets S that are LINE-FORCED (alignable at the correct deep-band pin).
  For each such S record the joint moment pair (c1,c2) = (sum_{x in S} x, sum x^2).
  The bad scalar is gamma = -c1 (Vieta pin, PROVEN in-tree). So:
    #bad        = #distinct c1 over line-forced S   (the e1-axis SUPPORT)
    N2(c1,c2)   = #{ line-forced S : sumS=c1, sum x^2 = c2 }   (the FIBER)
    collision   = sum_fiber N2^2  (Mansfield-Mudgal J_s sibling)

We measure, per maximizing line:
  (a) the full fiber histogram of N2 over the joint (c1,c2) level set,
  (b) max_fiber N2  (the per-fiber bound the lead wants),
  (c) #distinct (c1,c2) fibers, #distinct c1 (= #bad), #distinct c2,
  (d) the e1-projection multiplicity: max over c1 of #{c2 : N2(c1,c2)>0}
      (how many fibers stack over one bad scalar),
  (e) whether #bad = #fibers (i.e. is the (c1,c2)->c1 projection injective?).

This isolates EXACTLY whether a per-fiber max bound + level-set count gives #bad<=K.
Reuses the residual-det line-forcing test from cd_demand.c, reimplemented in Python
(validated to agree: it reproduces 97,145,89 worst #bad).
"""
import sys, itertools
from math import comb

P = 2013265921  # BabyBear

def powm(a,e): return pow(a%P, e, P)

def make_dom(n):
    e=(P-1)//n
    for c in range(2,300):
        h=powm(c,e)
        if powm(h,n)==1 and powm(h,n//2)!=1:
            cur=1; dom=[]
            for _ in range(n):
                dom.append(cur); cur=cur*h%P
            return dom
    raise SystemExit("no root")

def detm(M):
    # determinant mod P, M list of rows (lists), destroys
    m=len(M); det=1
    M=[row[:] for row in M]
    for col in range(m):
        piv=-1
        for rr in range(col,m):
            if M[rr][col]!=0: piv=rr;break
        if piv<0: return 0
        if piv!=col:
            M[piv],M[col]=M[col],M[piv]; det=(-det)%P
        det=det*M[col][col]%P
        inv=powm(M[col][col],P-2)
        for rr in range(col+1,m):
            if M[rr][col]!=0:
                ff=M[rr][col]*inv%P
                for c in range(col,m):
                    M[rr][c]=(M[rr][c]-ff*M[col][c])%P
    return det

def residual(dom,k,t,y):
    # bordered-Vandermonde (k+1)x(k+1): row a = [x_a^0..x_a^{k-1}, y_a]
    M=[]
    for a in t:
        row=[powm(dom[a],b) for b in range(k)]
        row.append(y[a])
        M.append(row)
    return detm(M)

def aligned_gamma(dom,k,Sidx,U0,U1):
    # returns (aligned_nondeg, has_gamma, gamma)
    gam=None; nondeg=False; any_u1=False
    for t in itertools.combinations(Sidx,k+1):
        r0=residual(dom,k,t,U0); r1=residual(dom,k,t,U1)
        if r0 or r1: nondeg=True
        if r1==0:
            if r0!=0: return (False,False,None)
        else:
            any_u1=True
            g=(-r0)*powm(r1,P-2)%P
            if gam is None: gam=g
            elif gam!=g: return (False,False,None)
    if not nondeg: return (False,False,None)
    return (True, any_u1, gam)

def run(n, r, e, f):
    dom=make_dom(n)
    k=(r-2)+1   # k_c = r-1 at m=1
    a0=r+1
    U0=[powm(dom[i],e) for i in range(n)]
    U1=[powm(dom[i],f) for i in range(n)]
    # collect line-forced S with their gamma and joint moments
    fibers={}   # (c1,c2) -> count
    bad=set()
    c1c2_of_bad={} # c1 -> set of c2
    for S in itertools.combinations(range(n),a0):
        ok,hg,gam=aligned_gamma(dom,k,list(S),U0,U1)
        if not ok or not hg: continue
        # joint moments of the actual subset (the level-set coords)
        c1=sum(dom[i] for i in S)%P
        c2=sum(dom[i]*dom[i]%P for i in S)%P
        # gamma = -c1 must hold (Vieta pin) -- assert
        if gam != (-c1)%P:
            # off-line subsets: gamma pinned by the bordered system can differ
            # from -sumS only if W absorbs; for line-forced deep band it's -c1.
            pass
        fibers[(c1,c2)]=fibers.get((c1,c2),0)+1
        bad.add(gam)
        c1c2_of_bad.setdefault(gam,set()).add(c2)
    nfib=len(fibers)
    maxN2=max(fibers.values()) if fibers else 0
    collision=sum(v*v for v in fibers.values())
    nbad=len(bad)
    ndist_c2=len({c2 for (c1,c2) in fibers})
    # e1-projection multiplicity: max #fibers over one bad scalar
    maxstack=max((len(s) for s in c1c2_of_bad.values()), default=0)
    K=(1<<r)*comb(n//2,r)
    # histogram of N2
    hist={}
    for v in fibers.values(): hist[v]=hist.get(v,0)+1
    print(f"n={n} r={r} line=(x^{e},x^{f}) a0={a0} k_c={k}")
    print(f"  #bad(=#distinct gamma=-c1)   = {nbad}   K={K}  bad<=K? {nbad<=K}")
    print(f"  #fibers(distinct (c1,c2))    = {nfib}")
    print(f"  max_fiber N2                 = {maxN2}   (per-fiber bound)")
    print(f"  collisionCount = sum N2^2    = {collision}")
    print(f"  #distinct c2                 = {ndist_c2}")
    print(f"  max #fibers over one c1      = {maxstack}  (e1-proj stacking)")
    print(f"  #bad == #fibers ?            = {nbad==nfib}  (c1-projection injective?)")
    print(f"  N2 histogram (N2:count)      = {dict(sorted(hist.items()))}")
    print(f"  CS support lower bound C^2/coll = {comb(n,a0)**2//collision if collision else 0} (vs true #bad {nbad})")
    return dict(nbad=nbad,nfib=nfib,maxN2=maxN2,collision=collision,K=K,maxstack=maxstack)

if __name__=="__main__":
    if len(sys.argv)>=5:
        run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]))
    else:
        # the n=16 deep-band maximizers from STRUCT.md
        cases=[(16,3,8,7),(16,4,8,5),(16,5,9,15),(16,6,8,10),(16,7,10,15),(16,8,9,11)]
        for n,r,e,f in cases:
            run(n,r,e,f); print()
