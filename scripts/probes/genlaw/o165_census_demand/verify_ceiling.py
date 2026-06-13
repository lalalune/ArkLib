# VERIFICATION: reproduce the known KKH26 supply at the CEILING band a=rm (not deep a0=rm+1),
# to confirm the alignment test is correct. KKH26 says #alignable rm-sets >= 2^r*C(n/2,r) at
# the ceiling for the monomial stack. Also test deep band a0 with a NON-monomial trapped stack.
from math import comb
from itertools import combinations
p = 2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,200):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
    raise RuntimeError
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
def count_align(n,r,a,kc,dom,u0,u1):
    alignable=0; badscalars=set()
    for S in combinations(range(n), a):
        pts=[dom[i] for i in S]
        c0=interp_coeffs(pts,[u0[i] for i in S]); c1=interp_coeffs(pts,[u1[i] for i in S])
        if c0 is None or c1 is None: continue
        gam=None; consistent=True; nondeg=False
        for j in range(kc,a):
            cc0=c0[j]; cc1=c1[j]
            if cc0!=0 or cc1!=0: nondeg=True
            if cc1==0:
                if cc0!=0: consistent=False; break
            else:
                g=(-cc0*pow(cc1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: consistent=False; break
        if consistent and nondeg:
            alignable+=1
            if gam is not None: badscalars.add(gam)
    return alignable, len(badscalars)
n=16
print("=== VERIFY: KKH26 monomial stack at CEILING band a=rm vs DEEP band a=rm+1 ===")
print(f"{'r':>3} {'kc':>3} {'a=rm(ceil)':>10} {'#align@ceil':>11} {'#bad@ceil':>9} | {'a0=rm+1(deep)':>13} {'#align@deep':>11} {'2^r*C(n/2,r)':>12}")
for r in range(2,6):
    kc=(r-2)+1; rm=r; a0=r+1
    dom=mu_n(n)
    u0=[pow(dom[i], r, p) for i in range(n)]; u1=[pow(dom[i], r-1, p) for i in range(n)]
    ac,bc=count_align(n,r,rm,kc,dom,u0,u1)
    ad,bd=count_align(n,r,a0,kc,dom,u0,u1)
    K=(1<<r)*comb(n//2,r)
    print(f"{r:>3} {kc:>3} {rm:>10} {ac:>11} {bc:>9} | {a0:>13} {ad:>11} {K:>12}")
