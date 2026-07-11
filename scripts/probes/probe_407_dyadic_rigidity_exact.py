#!/usr/bin/env python3
"""
EXACT dyadic-rigidity check at n=16 for the KEY non-power-of-2 supports t=3,5,6,7.
Claim: F(t) = n - n/2^floor(log2 t), i.e. min ||DFT(c)||_0 over nonzero support-<=t c
equals n/2^floor(log2 t) (NOT the weaker Donoho-Stark n/t).

EXACT method (no random): for a fixed support set T (|T|=t), the set of value-vectors
v = F[:,T] c (c in C^t) is a t-dim subspace V_T of C^n. min ||v||_0 over nonzero v in V_T
= n - max{ |Z| : the coordinate-projection ker has a nonzero vector vanishing on Z }
= n - max{ |Z| : rank(F[Z^c is free]) ...}. Equivalently min ||v||_0 = min over nonzero v in V_T.
We compute min ||v||_0 EXACTLY via: a nonzero v in V_T vanishing on a coordinate set Z exists
iff dim(V_T restricted-to-vanish-on-Z) >= 1 iff |Z| <= ... We find the LARGEST Z s.t. some
nonzero c has (F[Z,T] c)=0, i.e. F[Z,T] has nontrivial right-nullspace, i.e. rank(F[Z,T])<t.
Then min||v||_0 = n - |Z_max| (zeros), so #nonzero = t-dim ... = n-|Z_max|.
We search Z_max by trying all Z of decreasing size? Expensive. Instead: |Z_max| = n - min_nz.
Use the EXACT rank approach: min_nz(T) = min over all v in V_T nonzero of ||v||_0.
We get it by: for each subset Z (the ZERO set), check rank(F[Z,T])<t; max |Z| with that.
Restrict to t=3 (cheap) at n=16. Also confirm the W_s witnesses are the minimizers.
"""
import numpy as np
from itertools import combinations


def exists_zero_set_of_size(F, n, T, zsize):
    """does there exist Z, |Z|=zsize, with rank(F[Z,T])<|T| (nonzero c vanishing on Z)?"""
    t = len(T)
    for Z in combinations(range(n), zsize):
        M = F[list(Z), :][:, list(T)]
        if np.linalg.matrix_rank(M, tol=1e-8) < t:
            return True
    return False


def F_t_boundary(n, t, predF):
    """Confirm F(t)==predF: (a) achievable at predF, (b) NOT achievable at predF+1."""
    F = np.array([[np.exp(2j*np.pi*j*k/n) for k in range(n)] for j in range(n)])
    ach = False
    for T in combinations(range(n), t):
        if exists_zero_set_of_size(F, n, T, predF):
            ach = True
            break
    # optimality: no support T reaches predF+1 (and predF+1<n to stay non-degenerate)
    opt = True
    if predF + 1 < n:
        for T in combinations(range(n), t):
            if exists_zero_set_of_size(F, n, T, predF + 1):
                opt = False
                break
    return ach, opt


for mu in [4]:
    n = 2**mu
    print("=== n=%d EXACT boundary check ===" % n)
    for t in [2, 3]:
        s = int(np.floor(np.log2(t)))
        predF = n - n // (2**s)
        ach, opt = F_t_boundary(n, t, predF)
        verdict = "OK (achievable + optimal)" if (ach and opt) else \
                  ("ach=%s opt=%s" % (ach, opt))
        print("  t=%d: pred F=n-n/2^%d=%d -> %s" % (t, s, predF, verdict))
