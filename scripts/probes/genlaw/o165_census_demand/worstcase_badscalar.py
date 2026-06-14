# [MEASURED-FAITHFUL] Worst-case BAD-SCALAR count over stacks at the deep-band pin, n=16,
# faithful BabyBear. The bad-scalar count = #distinct gamma pinned by an alignable a0-set with a
# GENUINE non-joint witness (real mcaEvent). This is the demand quantity controlling delta*.
from math import comb
from itertools import combinations
import random
p = 2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,200):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def interp_coeffs(pts, vals):
    m=len(pts)
    A=[[pow(pts[i],j,p) for j in range(m)] for i in range(m)]
    M=[A[i][:]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        inv=pow(M[col][col],p-2,p); M[col]=[(v*inv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                f=M[rr][col]; M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]
def badscalar_count(n,a,k,dom,u0,u1):
    # real mcaEvent: alignable a0-set with gamma, NON-joint (not both u0,u1 codewords on S)
    bad=set()
    for S in combinations(range(n), a):
        pts=[dom[i] for i in S]
        c0=interp_coeffs(pts,[u0[i] for i in S]); c1=interp_coeffs(pts,[u1[i] for i in S])
        if c0 is None or c1 is None: continue
        gam=None; ok=True
        for j in range(k,a):
            x0=c0[j]; x1=c1[j]
            if x1==0:
                if x0: ok=False; break
            else:
                g=(-x0*pow(x1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: ok=False; break
        if ok and gam is not None:
            # non-joint: not (u0 cw on S and u1 cw on S)
            if not (all(c==0 for c in c0[k:]) and all(c==0 for c in c1[k:])):
                bad.add(gam)
    return len(bad)
n=16; rng=random.Random(11)
print("=== [MEASURED-FAITHFUL] worst-case BAD-SCALAR count at deep band, n=16, BabyBear ===")
for r in [3,4,5]:
    k=(r-2)+1; a0=r+1; dom=mu_n(n); K=(1<<r)*comb(n//2,r)
    best=0; bn=""
    # all monomial pairs
    for e in range(n):
        for f in range(n):
            if e==f: continue
            u0=[pow(x,e,p) for x in dom]; u1=[pow(x,f,p) for x in dom]
            b=badscalar_count(n,a0,k,dom,u0,u1)
            if b>best: best=b; bn=f"mono x^{e},x^{f}"
    # random + structured
    for _ in range(50):
        u0=[rng.randrange(p) for _ in range(n)]; u1=[rng.randrange(p) for _ in range(n)]
        b=badscalar_count(n,a0,k,dom,u0,u1)
        if b>best: best=b; bn="random"
    for d in [2,4]:
        for _ in range(30):
            deg=rng.randint(1,n//d); cf=[rng.randrange(p) for _ in range(deg+1)]
            u0=[sum(cf[t]*pow(pow(x,d,p),t,p) for t in range(deg+1))%p for x in dom]
            u1=[pow(x,r-1,p) for x in dom]
            b=badscalar_count(n,a0,k,dom,u0,u1)
            if b>best: best=b; bn=f"P(x^{d}),x^(r-1)"
    print(f" r={r} k={k} a0={a0}: WORST bad-scalar count = {best} ({bn})   K={K}   margin K/bad = {K/max(best,1):.0f}x   bad<=K? {best<=K}")
