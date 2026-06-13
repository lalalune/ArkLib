# Independent THIRD-method recount of the tightest n=16 deep band (r=7, a0=8, kc=6),
# worst-case stack mono x^10,x^15. Two methods in ONE script, must agree with C kernel (225).
#  (A) interp-coeff: top (a0-kc) coeffs of interpolant of w=u0+gamma*u1 vanish.
#  (B) residual-det: bordered Vandermonde det over all (kc+1)-subtuples (Lean ground truth).
from math import comb
from itertools import combinations
p=2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,300):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def interp_coeffs(pts,vals):
    m=len(pts); M=[[pow(pts[i],j,p) for j in range(m)]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]; inv=pow(M[col][col],p-2,p); M[col]=[(v*inv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                f=M[rr][col]; M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]
def det(M):
    m=len(M); M=[row[:] for row in M]; d=1
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return 0
        if piv!=col: M[col],M[piv]=M[piv],M[col]; d=(-d)%p
        d=(d*M[col][col])%p; inv=pow(M[col][col],p-2,p)
        for rr in range(col+1,m):
            if M[rr][col]%p!=0:
                f=(M[rr][col]*inv)%p; M[rr]=[(M[rr][c]-f*M[col][c])%p for c in range(m)]
    return d%p
def residual(dom,k,t,y):
    return det([[ (pow(dom[t[a]],b,p) if b<k else y[t[a]]) for b in range(k+1)] for a in range(k+1)])
n=16; r=7; kc=6; a0=8; dom=mu_n(n); K=(1<<r)*comb(n//2,r)
e,f=10,15
u0=[pow(x,e,p) for x in dom]; u1=[pow(x,f,p) for x in dom]
# Method A
badA=set(); alA=0
for S in combinations(range(n),a0):
    pts=[dom[i] for i in S]
    c0=interp_coeffs(pts,[u0[i] for i in S]); c1=interp_coeffs(pts,[u1[i] for i in S])
    gam=None; ok=True; nd=False
    for j in range(kc,a0):
        x0,x1=c0[j],c1[j]
        if x0 or x1: nd=True
        if x1==0:
            if x0: ok=False; break
        else:
            g=(-x0*pow(x1,p-2,p))%p
            if gam is None: gam=g
            elif gam!=g: ok=False; break
    if ok and nd:
        alA+=1
        if gam is not None: badA.add(gam)
# Method B
badB=set(); alB=0
for S in combinations(range(n),a0):
    gam=None; ok=True; nd=False
    for tt in combinations(S,kc+1):
        t=list(tt); r0=residual(dom,kc,t,u0); r1=residual(dom,kc,t,u1)
        if r0 or r1: nd=True
        if r1==0:
            if r0: ok=False; break
        else:
            g=(-r0*pow(r1,p-2,p))%p
            if gam is None: gam=g
            elif gam!=g: ok=False; break
    if ok and nd:
        alB+=1
        if gam is not None: badB.add(gam)
print(f"n=16 r=7 a0=8 kc=6 stack x^{e},x^{f}: K={K} pack={comb(n,a0)//(a0+1)}")
print(f"  Method A (interp-coeff): #align={alA} #bad={len(badA)}")
print(f"  Method B (residual-det): #align={alB} #bad={len(badB)}")
print(f"  AGREE: align={alA==alB} bad={len(badA)==len(badB)}  (C kernel reported #bad=225)")
print(f"  bad<=K? {len(badB)<=K}  bad<=pack? {len(badB)<=comb(n,a0)//(a0+1)}")
