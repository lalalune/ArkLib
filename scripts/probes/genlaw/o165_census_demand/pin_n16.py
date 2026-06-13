# [COMPUTED] Exact deep-band #bad-scalar AND #alignable-a-set count for the KKH26 worst-case
# stack (u0=X^{rm}, u1=X^{(r-1)m}) over mu_n, faithful BabyBear prime. m=1, n=16.
# Demand side (complement of O164 fiber/supply side). Exact integer arithmetic, no sampling.
from math import comb
from itertools import combinations

p = 2013265921  # BabyBear, faithful (p^2 >> C(16,8)=12870)

def mu_n(n):
    # primitive n-th root of unity: g = generator^((p-1)/n)
    # p-1 = 15*2^27; find a generator of order n
    e=(p-1)//n
    for c in range(2,200):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in (2,)):  # n=2^mu so only q=2
            return [pow(h,i,p) for i in range(n)]
    raise RuntimeError("no root")

def interp_coeffs(pts, vals):
    # interpolant of degree < len(pts) through (pts,vals); return coeff list low->high
    m=len(pts)
    A=[[pow(pts[i],j,p) for j in range(m)] for i in range(m)]
    M=[A[i][:]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        inv=pow(M[col][col],p-2,p)
        M[col]=[(v*inv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                f=M[rr][col]; M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]

def run(n, r):
    m=1; kc=(r-2)*m+1; a0=r*m+1   # k_c, a0; band a=a0 (deepest in this band)
    dom=mu_n(n)
    # KKH26 worst-case stack: u0[i]=dom[i]^(r*m), u1[i]=dom[i]^((r-1)*m)
    u0=[pow(dom[i], r*m, p) for i in range(n)]
    u1=[pow(dom[i], (r-1)*m, p) for i in range(n)]
    K=(1<<r)*comb(n//2, r)
    # DEMAND SIDE: enumerate all a0-subsets S. S is alignable iff line u0+gamma*u1 restricted to
    # S is explainable by deg < k_c codeword for SOME gamma, with a non-degenerate tuple.
    # Mechanism (q-independence): the (k_c+1)-residuals of u0,u1 on S must be proportional with
    # ONE common ratio gamma. Equivalently: there is gamma s.t. (u0+gamma*u1)|_S agrees with a
    # poly of degree < k_c. Test: interpolant of u0 and of u1 on S each have degree < a0; the
    # combined w=u0+gamma*u1 has interpolant deg < k_c iff its top (a0-k_c) coeffs vanish.
    # The top coeff of w-interp = c0[j]+gamma*c1[j] for j=k_c..a0-1. Non-degenerate => not both 0.
    alignable=0
    badscalars=set()
    for S in combinations(range(n), a0):
        pts=[dom[i] for i in S]
        c0=interp_coeffs(pts,[u0[i] for i in S])
        c1=interp_coeffs(pts,[u1[i] for i in S])
        if c0 is None or c1 is None: continue
        # need gamma s.t. c0[j]+gamma*c1[j]=0 for all j in [k_c, a0-1] (the (a0-k_c) top coeffs)
        # i.e. all those constraints share a single gamma. Non-degenerate: some j has (c0[j],c1[j])!=(0,0).
        Js=list(range(kc,a0))
        gam=None; consistent=True; nondeg=False
        for j in Js:
            cc0=c0[j]; cc1=c1[j]
            if cc0!=0 or cc1!=0: nondeg=True
            if cc1==0:
                if cc0!=0: consistent=False; break   # 0=cc0 impossible
                # else 0=0, no constraint
            else:
                g=(-cc0*pow(cc1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: consistent=False; break
        if consistent and nondeg:
            alignable+=1
            if gam is not None: badscalars.add(gam)
            # gam==None means all top coeffs already 0 with cc1==0,cc0==0 -> degenerate-ish; needs nondeg via lower
    return dict(n=n,r=r,kc=kc,a0=a0,K=K,Cn_a0=comb(n,a0),
                pack=comb(n,a0)//(a0+1),
                alignable=alignable, badscalars=len(badscalars))

import time
print("=== [COMPUTED] KKH26 worst-case stack, n=16, faithful BabyBear, deep band ===")
print(f"{'r':>3} {'kc':>3} {'a0':>3} {'C(16,a0)':>9} {'#alignable':>11} {'#badscal':>9} {'K=budget':>9} {'pack':>6} {'alignable<=K?':>13} {'bad<=K?':>8}")
for r in range(2,9):  # r=2..8 (n/2=8); deep band r in [sqrt(16ln16)=6.6 -> 7,8] but show all
    t0=time.time()
    d=run(16,r)
    print(f"{d['r']:>3} {d['kc']:>3} {d['a0']:>3} {d['Cn_a0']:>9} {d['alignable']:>11} {d['badscalars']:>9} {d['K']:>9} {d['pack']:>6} {str(d['alignable']<=d['K']):>13} {str(d['badscalars']<=d['K']):>8}  ({time.time()-t0:.1f}s)")
