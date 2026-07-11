#!/usr/bin/env python3
"""
Corrected exact-arithmetic probe for the #371 WB window residual at (13,6,1,2).

FAITHFUL WBSolvable: y is WB-solvable at (k,w) iff the n x ((w+1)+(w+k)) WB matrix
   M(y)[i] = [ x_i^t * y_i (t=0..w) | -x_i^s (s=0..w+k-1) ]
has a nontrivial kernel  <=>  rank < (2w+k+1).  At n=2w+k+1 this is det M(y)=0.
This INCLUDES genuine rational functions R/l (l non-vanishing on D) that are far
from every codeword -- the stratum the previous probe missed.

mcaEvent (k=1): exists S, |S|>=n-w, line u0+gamma*u1 constant on S, and NOT
(u0 constant on S AND u1 constant on S).
"""
import itertools, random

q = 13
n = 6
k = 1
w = 2
need = n - w     # 4
NCOL = (w+1) + (w+k)   # 3 + 3 = 6

def order_subgroup(q, n):
    for cand in range(2, q):
        seen=set(); x=1
        for _ in range(q-1):
            x=(x*cand)%q; seen.add(x)
        if len(seen)==q-1:
            g=cand; break
    h=pow(g,(q-1)//n,q)
    return sorted({pow(h,j,q) for j in range(n)})

D = order_subgroup(q,n)
inv = {x:pow(x,q-2,q) for x in D if x}
sigma = {x:(-pow(x,q-2,q))%q for x in D}
idx = {x:i for i,x in enumerate(D)}

def orbits_of(perm,dom):
    seen=set(); orbs=[]
    for x in dom:
        if x in seen: continue
        o=[x]; seen.add(x); y=perm[x]
        while y!=x:
            o.append(y); seen.add(y); y=perm[y]
        orbs.append(tuple(sorted(o)))
    return orbs
SIGMA_ORBITS=orbits_of(sigma,D)
SUBSETS_GE=[S for r in range(need,n+1) for S in itertools.combinations(range(n),r)]

def det_mod(M,p):
    """determinant of square matrix M over GF(p) via Gaussian elimination."""
    M=[row[:] for row in M]; N=len(M); det=1
    for c in range(N):
        piv=None
        for r in range(c,N):
            if M[r][c]%p!=0: piv=r; break
        if piv is None: return 0
        if piv!=c:
            M[c],M[piv]=M[piv],M[c]; det=(-det)%p
        invp=pow(M[c][c],p-2,p); det=(det*M[c][c])%p
        for r in range(c+1,N):
            f=(M[r][c]*invp)%p
            if f:
                for cc in range(c,N):
                    M[r][cc]=(M[r][cc]-f*M[c][cc])%p
    return det%p

def wb_matrix(y):
    M=[]
    for i,x in enumerate(D):
        row=[ (pow(x,t,q)*y[i])%q for t in range(w+1) ] + \
            [ (-pow(x,s,q))%q for s in range(w+k) ]
        M.append(row)
    return M

def wb_solvable(y):
    # n == NCOL == 6 here: singular square matrix <=> nontrivial kernel
    return det_mod(wb_matrix(y),q)==0

def joint_on_S(u0,u1,S):
    return len({u0[i] for i in S})==1 and len({u1[i] for i in S})==1

def line_const_on_S(u0,u1,g,S):
    return len({(u0[i]+g*u1[i])%q for i in S})==1

def is_bad(u0,u1,g):
    for S in SUBSETS_GE:
        if line_const_on_S(u0,u1,g,S) and not joint_on_S(u0,u1,S):
            return True
    return False

def bad_set(u0,u1):
    return [g for g in range(q) if is_bad(u0,u1,g)]

print(f"mu_{n} in F_{q}: {D}")
print(f"sigma orbits: {SIGMA_ORBITS}; need={need}, NCOL={NCOL}\n")

# all WBSolvable rows (faithful), full enumeration over F_13^6 is 4.8M (too slow in
# python for pairs); use sigma-invariant family for exhaustive extremal search.
def make_sig_inv(combo):
    u=[0]*n
    for j,orb in enumerate(SIGMA_ORBITS):
        for x in orb: u[idx[x]]=combo[j]
    return tuple(u)

sig_rows=[make_sig_inv(c) for c in itertools.product(range(q),repeat=len(SIGMA_ORBITS))]
sig_solv=[r for r in sig_rows if wb_solvable(r)]
print(f"sigma-invariant rows={len(sig_rows)}, WBSolvable={len(sig_solv)}")

best=(-1,None,None,None)
for u0 in sig_solv:
    for u1 in sig_solv:
        bs=bad_set(u0,u1)
        if len(bs)>best[0]:
            best=(len(bs),u0,u1,bs)
print(f"[sigma-invariant] MAX bad = {best[0]}  (w+1={w+1})")
print(f"   extremal u0={best[1]} u1={best[2]} bad={best[3]}")

# sample GENERAL WBSolvable pairs (rejection sampling) for the cap
random.seed(2)
def rand_solv():
    while True:
        y=tuple(random.randrange(q) for _ in range(n))
        if wb_solvable(y): return y
gmax=(-1,None,None,None)
for _ in range(60000):
    u0=rand_solv(); u1=rand_solv()
    bs=bad_set(u0,u1)
    if len(bs)>gmax[0]:
        gmax=(len(bs),u0,u1,bs)
print(f"[general WBSolvable, 60k samples] MAX bad = {gmax[0]}")
print(f"   u0={gmax[1]} u1={gmax[2]} bad={gmax[3]}\n")

# ---- structural analysis of the extremal via its rational representation ----
def rational_reps(y):
    """all (l_coeffs, R_coeffs) with deg l<=w, deg R<=w+k-1, l!=0,
       l(x_i) y_i = R(x_i) on D, l monic-normalized (leading nonzero coeff=1)."""
    reps=[]
    # enumerate l (deg<=w) up to scaling: normalize first nonzero coeff =1
    for lc in itertools.product(range(q),repeat=w+1):
        if all(c==0 for c in lc): continue
        # normalize: leading (highest) nonzero coeff -> 1
        hi=max(t for t in range(w+1) if lc[t]!=0)
        if lc[hi]!=1: continue
        # solve R from R(x_i)=l(x_i) y_i ; R determined by deg<=w+k-1 interpolation
        # check consistency: the points (x_i, l(x_i) y_i) must lie on a deg<=w+k-1 poly
        pts=[]
        for i,x in enumerate(D):
            lx=sum(lc[t]*pow(x,t,q) for t in range(w+1))%q
            pts.append((x,(lx*y[i])%q))
        # fit: does a poly of degree <= w+k-1 pass through all pts? (n points)
        # build Vandermonde deg w+k-1 (=2 here, 3 coeffs) and check solvability
        degR=w+k-1
        A=[[pow(x,j,q) for j in range(degR+1)] for (x,_) in pts]
        b=[v for (_,v) in pts]
        sol=solve_mod(A,b,q)
        if sol is not None:
            reps.append((lc,tuple(sol)))
    return reps

def solve_mod(A,b,p):
    """least-structure: return a solution vector x with A x = b over GF(p), or None."""
    A=[row[:] for row in A]; b=b[:]; rows=len(A); cols=len(A[0])
    where=[-1]*cols; r=0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if A[i][c]%p: piv=i; break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; b[r],b[piv]=b[piv],b[r]
        invp=pow(A[r][c],p-2,p)
        A[r]=[(v*invp)%p for v in A[r]]; b[r]=(b[r]*invp)%p
        for i in range(rows):
            if i!=r and A[i][c]%p:
                f=A[i][c]
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(cols)]
                b[i]=(b[i]-f*b[r])%p
        where[c]=r; r+=1
    for i in range(rows):
        if all(A[i][j]%p==0 for j in range(cols)) and b[i]%p!=0:
            return None
    x=[0]*cols
    for c in range(cols):
        if where[c]!=-1: x[c]=b[where[c]]%p
    return x

def poly_eval(coeffs,x):
    return sum(coeffs[j]*pow(x,j,q) for j in range(len(coeffs)))%q

print(f"--- rational reps of extremal rows ---")
for tag,row in [("u0",best[1]),("u1",best[2])]:
    reps=rational_reps(row)
    print(f"  {tag}={row}: {len(reps)} rational reps; sample: {reps[:2]}")
print()

# Mobius invariance
def apply_sigma(u):
    out=[0]*n
    for x in D: out[idx[sigma[x]]]=u[idx[x]]
    return tuple(out)
u0s,u1s=apply_sigma(best[1]),apply_sigma(best[2])
print(f"[Mobius] sigma-image: u0'={u0s} u1'={u1s} bad={bad_set(u0s,u1s)}")
print(f"   sigma-invariant? u0:{u0s==best[1]} u1:{u1s==best[2]}")
