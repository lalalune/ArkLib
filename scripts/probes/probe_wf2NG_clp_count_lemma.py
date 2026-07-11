#!/usr/bin/env python3
"""
wf-NG (#407): the DECISIVE pinning probe for the partition/analytic-rank / multiplicative-CLP
lane. Three machine-checked obstructions on the cyclotomic relation tensor
   S(a_1..a_r) = 1 iff zeta^{a_1}+...+zeta^{a_r}=0 (n-th roots, n=2^mu), indices a_i in Z/n.
|support(S)| = N0(mu_n,r) = the §407 open object.

(1) support is 100% OFF-diagonal {(a,..,a)} -> Tao/Naslund COUNT theorem bounds the empty
    diagonal (vacuous), even after multiplicative re-indexing.
(2) single-mode line-size <=1 (favorable matching) yet slice/partition rank = FULL n; the
    method's only output r*n is a FALSE bound on N0 (N0(8,4)=168 > r*n=32).
(3) the index group Z/2^mu is CYCLIC (d=1), not a cube (Z/2)^mu -> zero CLP/EG saving.
"""
import itertools, numpy as np

def roots(n):
    d=n//2; out=[]
    for k in range(n):
        v=[0]*d; s=1; kk=k%n
        while kk>=d: kk-=d; s=-s
        v[kk]=s; out.append(tuple(v))
    return out

def build_S(n,r):
    R=roots(n); d=n//2; S=np.zeros((n,)*r,dtype=np.int64)
    for idx in itertools.product(range(n),repeat=r):
        acc=[0]*d
        for a in idx:
            for t in range(d): acc[t]+=R[a][t]
        if all(x==0 for x in acc): S[idx]=1
    return S

def diag_off(S):
    r=S.ndim; n=S.shape[0]; dg=0; off=0
    for idx in itertools.product(range(n),repeat=r):
        if S[idx]:
            if len(set(idx))==1: dg+=1
            else: off+=1
    return dg,off

def max_line(S):
    r=S.ndim; n=S.shape[0]; best=0
    for mode in range(r):
        other=[m for m in range(r) if m!=mode]
        for fx in itertools.product(range(n),repeat=len(other)):
            c=0
            for xm in range(n):
                idx=[0]*r; idx[mode]=xm
                for j,m in enumerate(other): idx[m]=fx[j]
                c+=int(S[tuple(idx)])
            best=max(best,c)
    return best

def slice_rank(S):
    r=S.ndim; n=S.shape[0]; best=None
    for i in range(r):
        perm=[i]+[m for m in range(r) if m!=i]
        M=np.transpose(S,perm).reshape(n,n**(r-1)).astype(float)
        rk=int(round(np.linalg.matrix_rank(M)))
        best=rk if best is None else min(best,rk)
    return best

if __name__=="__main__":
    print("=== wf-NG DECISIVE: 3 obstructions on the cyclotomic relation tensor ===")
    print(f"{'n':>4} {'r':>3} {'N0':>6} {'diag':>5} {'offdiag':>8} {'maxLine':>8} {'sliceRk':>8} {'r*Rk(bound)':>11} {'bound<N0?(FALSE)':>16}")
    for n in [4,8,16]:
        for r in [2,3,4]:
            if n==16 and r>3: continue
            S=build_S(n,r); nz=int(S.sum()); dg,off=diag_off(S)
            ml=max_line(S); sr=slice_rank(S); bound=r*sr
            false_bound = (bound < nz) and nz>0
            print(f"{n:>4} {r:>3} {nz:>6} {dg:>5} {off:>8} {ml:>8} {sr:>8} {bound:>11} {str(false_bound):>16}")
    print()
    print("(1) diag=0 always: CLP/Tao count theorem (|X|<=r*rk for DIAGONAL tensor) is vacuous.")
    print("(2) maxLine<=1 (matching) but sliceRk=FULL n; r*Rk is a FALSE N0 bound (col flagged True).")
    print("(3) index group Z/2^mu CYCLIC (one factor) => no cube => no CLP/EG exponent saving.")
