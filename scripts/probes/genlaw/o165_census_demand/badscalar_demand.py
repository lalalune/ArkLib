# DECISIVE: distinguish #alignable-SETS (lossy intermediary) from #BAD-SCALARS (the true demand
# quantity = #{gamma : line delta-close with genuine non-joint witness}). For the "codeword-stack"
# adversaries that blew up #alignable to C(n,a), measure the ACTUAL bad-scalar count (distinct
# pinned gamma) AND the set-level mcaEvent count (with ¬pairJointAgreesOn, the real MCA def).
from math import comb
from itertools import combinations
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
def is_codeword_on_S(coeffs,k):
    # interpolant degree < k  <=> coeffs[k..]==0
    return all(c==0 for c in coeffs[k:])
def analyze(n,a,k,dom,u0,u1):
    align=0; badscal=set(); mcaTrue=0  # mcaTrue: alignable AND ¬pairJoint (real MCA def)
    for S in combinations(range(n), a):
        pts=[dom[i] for i in S]
        c0=interp_coeffs(pts,[u0[i] for i in S]); c1=interp_coeffs(pts,[u1[i] for i in S])
        if c0 is None or c1 is None: continue
        gam=None; ok=True; nd=False
        for j in range(k,a):
            x0=c0[j]; x1=c1[j]
            if x0 or x1: nd=True
            if x1==0:
                if x0: ok=False; break
            else:
                g=(-x0*pow(x1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: ok=False; break
        if ok and nd:
            align+=1
            if gam is not None: badscal.add(gam)
            # real MCA: NOT(u0 codeword on S AND u1 codeword on S)
            if not (is_codeword_on_S(c0,k) and is_codeword_on_S(c1,k)):
                mcaTrue+=1
    return align,len(badscal),mcaTrue
n=16
print("=== DEMAND vs LOSSY: #alignable-sets, #bad-scalars, #mcaEvent(real ¬pairJoint) ===")
print(f"{'r':>2} {'stack':>22} {'a0':>3} {'#alignSets':>10} {'#BADSCALARS':>11} {'#mcaEvt(real)':>13} {'K':>6} {'bad<=K?':>8}")
for r in [3,4,5]:
    k=(r-2)+1; a0=r+1; dom=mu_n(n); K=(1<<r)*comb(n//2,r)
    for (e,f,name) in [(r,r-1,"KKH26 x^r,x^{r-1}"),(1,3,"x^1,x^3 (u0 cw)"),(0,2,"x^0,x^2 (u0 cw)")]:
        u0=[pow(x,e,p) for x in dom]; u1=[pow(x,f,p) for x in dom]
        al,bs,mt=analyze(n,a0,k,dom,u0,u1)
        print(f"{r:>2} {name:>22} {a0:>3} {al:>10} {bs:>11} {mt:>13} {K:>6} {str(bs<=K):>8}")
