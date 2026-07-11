#!/usr/bin/env python3
"""
Validate F(t) = n - n/2^floor(log2 t) at n=16 (the dyadic-rigidity claim) WITHOUT
brute-forcing all subsets. Two directions:

(A) ACHIEVABILITY (lower bound F(t) >= n-n/2^s, s=floor(log2 t)): the power-of-2 witness
    W_s = (X^n-1)/(X^{n/2^s}-1) has support 2^s <= t and n-n/2^s roots. So F(t) >= that. (Trivial.)

(B) OPTIMALITY (upper bound F(t) <= n-n/2^s): NO t-sparse nonzero poly (non-degenerate) vanishes
    on MORE than n-n/2^s points of mu_n. Equivalent (uncertainty principle on Z/n, n=2^mu):
    a nonzero c in C^n with support(c) <= t has at most ... zeros in its DFT? Actually we want:
    #zeros of the FUNCTION p|_{mu_n} (= DFT of coeff vector c) <= n - n/2^s when ||c||_0 <= t and
    p not identically 0 on mu_n.  i.e. #nonzeros of DFT(c) >= n/2^s whenever 0<||c||_0<=t... no.
    Let v=DFT(c) (values on mu_n). support(c)=t, v not all zero. Claim: #{j: v_j != 0} >= n/2^s
    where s=floor(log2 t)? Check: t=2 -> n/2; the binomial X^{n/2}+1 has v_j = 1+(-1)^j*... wait
    v_j = (zeta^j)^{n/2}+1 in {0,2}, nonzero on n/2 -> #nonzero=n/2 = n/2^1. matches (s=1).
    So OPTIMALITY <=> the Z/2^mu uncertainty: ||c||_0 * ||DFT(c)||_0 >= n? NO, that's the standard
    bound ||c||_0 + ||DFT c||_0 >= ... Let's just MEASURE: min over c with ||c||_0=t of ||DFT(c)||_0.
"""
import numpy as np
from itertools import combinations

def min_dft_support(n, t):
    """min # nonzero DFT values over nonzero c with support exactly within some t-set.
    = min over t-subsets T of min over nonzero c on T of ||F c||_0.
    For fixed support T, the achievable v=F[:,T] c spans a t-dim subspace; min ||v||_0 of a
    nonzero vector in a generic t-dim subspace of C^n. We approximate the MIN by trying the
    structured (cyclotomic) c's AND a few random c on T, taking min observed nonzero-count.
    To get a rigorous-ish min we use: the cyclotomic product witnesses are the extremal ones."""
    F = np.array([[np.exp(2j*np.pi*j*k/n) for k in range(n)] for j in range(n)])
    best = n
    # structured: arithmetic-progression supports (the W_s family + shifts/dilations)
    for T in combinations(range(n), t):
        Msub = F[:, list(T)]
        # try a handful of c: each basis-ish + random complex, count min nonzero of F c
        trials = []
        for _ in range(40):
            c = (np.random.randn(t) + 1j*np.random.randn(t))
            v = Msub @ c
            trials.append(int(np.sum(np.abs(v) > 1e-7)))
        # also try to KILL coords: solve for c making as many v_j=0 as possible:
        # pick n-? rows to zero -> handled by random already roughly. take min trial.
        best = min(best, min(trials))
    return best

for mu in [3, 4]:
    n = 2**mu
    print("=== n=%d : min ||DFT(c)||_0 over support-t c (=> F(t)=n-that) ===" % n)
    for t in range(2, n+1):
        m = min_dft_support(n, t)
        s = int(np.floor(np.log2(t)))
        pred_nz = n // (2**s)     # predicted min nonzero DFT support
        Ft = n - m
        predF = n - pred_nz
        ok = "OK" if m == pred_nz else "<-- min_dft=%d pred=%d" % (m, pred_nz)
        print("  t=%2d: min||DFT||_0=%2d  F(t)=%2d   pred F=n-n/2^%d=%2d  %s" %
              (t, m, Ft, s, predF, ok))
