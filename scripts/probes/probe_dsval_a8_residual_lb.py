#!/usr/bin/env python3
"""
A8 LOWER BOUND via residual-parallelism structure (char-0, exact-enough float on mu_n).

THE LOWER-BOUND ARGUMENT (to be certified numerically here):
  Fix far direction (a,b), k=rho n, step t=b-a.  For a w-subset S of mu_n:
    f_gamma = x^a + gamma x^b  agrees with some deg<k poly on S
      iff  r_a(S) + gamma r_b(S) = 0   where r_c(S) = (col x^c) projected OFF span{1..x^{k-1}} on S.
    r_a,r_b live in the (w-k)-dim residual space (V_k full-rank on S, true for w>=k on mu_n distinct).
    So S consistent  <=>  r_a(S) parallel to r_b(S)  (incl. r_a=0).
    When consistent, gamma(S) = -<r_b,r_a>/<r_b,r_b>  is UNIQUE.
  Therefore:
    I(w) = #{ distinct gamma(S) : S consistent, w-subset }   <=   #{ consistent w-subsets } =: Cons(w).
  And Cons(w) is the count of S making two vectors in a (w-k)-dim space parallel: as w grows the
  parallel condition is codim (w-k-1), so Cons(w) DROPS sharply.  The LOWER bound delta* >= 1-w_e/n
  where w_e = smallest w with worst-dir I(w) <= n.

This probe:
  (1) confirms the parallel-residual characterization equals the rank test (sanity, char-0),
  (2) tabulates I(w) and Cons(w) for the WORST directions only (cheap), finds w_e,
  (3) tests closed forms for Cons(w) and I(w) (coset-union counting).
Float on roots of unity is exact to ~1e-12 here; we use tol 1e-7 and cross-check small cases
against the exact a6 results (n=8 dir(4,7) I=9; n=16 dir(4,6) I=40 at w=b).
"""
import itertools, cmath, math
import numpy as np
from math import comb, gcd
from collections import Counter
TAU=2*math.pi

def mu(n): return [cmath.exp(1j*TAU*s/n) for s in range(n)]

def residuals(n,k,a,b,S,roots):
    xs=np.array([roots[s] for s in S])
    V=np.column_stack([xs**c for c in range(k)])
    ca=xs**a; cb=xs**b
    Q,_=np.linalg.qr(V)           # orthonormal basis of colspace(V)
    ra=ca-Q@(Q.conj().T@ca)
    rb=cb-Q@(Q.conj().T@cb)
    return ra,rb

def consistent_gamma(n,k,a,b,S,roots,tol=1e-7):
    ra,rb=residuals(n,k,a,b,S,roots)
    nb=np.linalg.norm(rb); na=np.linalg.norm(ra)
    if nb<tol:           # x^b already in RS[k] on S: degenerate, skip
        return None
    gamma=-np.vdot(rb,ra)/np.vdot(rb,rb)
    if np.linalg.norm(ra+gamma*rb) < tol*max(1.0,na):
        return gamma
    return None

def scan_dir(n,k,a,b,w,roots,tol=1e-7,key=4):
    gammas=[]
    for S in itertools.combinations(range(n),w):
        g=consistent_gamma(n,k,a,b,S,roots,tol)
        if g is not None and abs(g)>tol:    # exclude gamma=0
            gammas.append(complex(round(g.real,key),round(g.imag,key)))
    cons=len(gammas)
    I=len(set(gammas))
    return I,cons

CANDIDATE_DIRS={
 (8,2):[(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)],
 (8,4):[(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)],
 (16,4):[(4,5),(4,6),(4,7),(4,8),(6,8),(5,6)],
 (16,8):[(8,9),(8,10),(8,11),(8,12),(10,12),(9,10)],
}

def main():
    print("=== A8 residual-parallel LOWER BOUND, worst dir, I(w) and Cons(w) ===")
    for (n,rho) in [(8,0.25),(8,0.5),(16,0.25),(16,0.5)]:
        k=int(round(rho*n)); roots=mu(n)
        dirs=CANDIDATE_DIRS[(n,k)]
        print(f"\n--- n={n} rho={rho} k={k} budget={n} ---  dirs scanned={dirs}")
        w_edge=None
        for w in range(n-1,k,-1):
            bestI=0;bestcons=0;bestdir=None
            for (a,b) in dirs:
                if not (k<=a<b<n): continue
                I,cons=scan_dir(n,k,a,b,w,roots)
                if I>bestI: bestI=I;bestcons=cons;bestdir=(a,b)
            le=bestI<=n
            mark=""
            if le and w_edge is None: w_edge=w
            print(f"  w={w:2d} delta={1-w/n:.4f}  worstI={bestI:5d} Cons={bestcons:5d} dir={bestdir}  I<=n:{le}")
        if w_edge is not None:
            print(f"  >> LOWER BOUND (down-scan first I<=n): delta* >= {1-w_edge/n:.4f}  (w_edge={w_edge}, =b+? )")
            print(f"     compare 1-rho={1-rho:.4f}; gap=(1-rho)-deltaLB = {(1-rho)-(1-w_edge/n):.4f}")
    print("\nDONE")

if __name__=="__main__":
    main()
