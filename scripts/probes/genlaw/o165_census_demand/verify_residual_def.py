# CORRECTNESS CHECK: implement the EXACT residual-based Aligned + nondegeneracy from the Lean
# defs, and compare to my interp-coeff test. residual dom k t y = det of bordered Vandermonde:
# columns: [x_a^0, x_a^1, ..., x_a^{k-1}, y(x_a)] for the (k+1)-tuple t. Aligned: for ALL
# injective (k+1)-tuples t in S, residual(u0)+gamma*residual(u1)=0. Nondeg: exists t in S with
# NOT(residual u0=0 AND residual u1=0). This is the GROUND TRUTH per the Lean files.
from math import comb
from itertools import combinations, permutations
p = 2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,200):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def det_mod(M):
    m=len(M); M=[row[:] for row in M]; det=1
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return 0
        if piv!=col: M[col],M[piv]=M[piv],M[col]; det=(-det)%p
        det=(det*M[col][col])%p; inv=pow(M[col][col],p-2,p)
        for rr in range(col+1,m):
            if M[rr][col]%p!=0:
                f=(M[rr][col]*inv)%p; M[rr]=[(M[rr][c]-f*M[col][c])%p for c in range(m)]
    return det%p
def residual(dom,k,t,y):
    # bordered matrix: rows a in 0..k, cols b: if b<k -> dom[t[a]]^b else y[t[a]]
    M=[[ (pow(dom[t[a]],b,p) if b<k else y[t[a]]) for b in range(k+1)] for a in range(k+1)]
    return det_mod(M)
def aligned_nondeg_count(n,a,k,dom,u0,u1):
    # for each a-subset S: find gamma s.t. residual(u0,t)+gamma*residual(u1,t)=0 for ALL inj (k+1)-tuples
    # t in S, AND some t nondegenerate. (k+1)-subsets of S; tuples = orderings but det only changes sign,
    # and ratio residual(u0)/residual(u1) is order-independent => use (k+1)-SUBSETS as tuples.
    al=0
    for S in combinations(range(n), a):
        gam=None; ok=True; nd=False
        for tt in combinations(S, k+1):
            t=list(tt)
            r0=residual(dom,k,t,u0); r1=residual(dom,k,t,u1)
            if r0 or r1: nd=True
            if r1==0:
                if r0: ok=False; break
            else:
                g=(-r0*pow(r1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: ok=False; break
        if ok and nd: al+=1
    return al
n=16
print("=== GROUND-TRUTH residual-det count vs interp-coeff count (must match) ===")
for r in [3]:
    k=(r-2)+1; a0=r+1; dom=mu_n(n)  # k = kc
    for (e,f,name) in [(r,r-1,"KKH26 x^r,x^{r-1}"),(0,2,"x^0,x^2 (u0=const)"),(1,3,"x^1,x^3")]:
        u0=[pow(x,e,p) for x in dom]; u1=[pow(x,f,p) for x in dom]
        c=aligned_nondeg_count(n,a0,k,dom,u0,u1)
        print(f" r={r} k={k} a0={a0} stack=({name}): residual-det #alignable = {c}")
