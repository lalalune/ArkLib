#!/usr/bin/env python3
"""
PROBE (rule 2): the DOUBLE-BLOCK (c=1 twisted) clique constraint-space finrank.

The c=1 single-block constraint space is ker(sumFunctional W) = {v : sum v = 0}, dim = w = |W|-1
(LANDED, finrank_cliqueSumKer). The DOUBLE-BLOCK (twisted) constraint space is the INF of two
hyperplanes:
    ker(sumFunctional)  cap  ker(twistFunctional gamma)
  = {v : sum_i v_i = 0  AND  sum_i gamma_i v_i = 0}.

Claim to pin: finrank = w - 1 = |W| - 2  IFF the two functionals are linearly independent
(equivalently: gamma is NOT constant on W, i.e. gamma takes >=2 distinct values -- because if
gamma_i = c for all i then twistFunctional = c * sumFunctional, proportional, and the inf collapses
back to the single hyperplane of dim w).

We Gaussian-eliminate the 2 x |W| constraint matrix [ 1...1 ; gamma_1...gamma_|W| ] over Q and over
F_p, and read nullity. We test BOTH branches:
  (a) gamma with >=2 distinct values (independent)   -> expect nullity = |W| - 2 = w - 1
  (b) gamma constant (proportional / dependent)       -> expect nullity = |W| - 1 = w
"""
from fractions import Fraction
import random

def nullity_Q(rows, ncol):
    # rows: list of lists of Fraction; returns dim of right-kernel over Q
    M = [r[:] for r in rows]
    nr = len(M)
    pivots = 0
    pivcols = []
    r = 0
    for c in range(ncol):
        # find pivot in column c at/below row r
        piv = None
        for i in range(r, nr):
            if M[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = M[r][c]
        M[r] = [x / inv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f*b for a,b in zip(M[i], M[r])]
        pivots += 1
        pivcols.append(c)
        r += 1
        if r == nr: break
    return ncol - pivots

def nullity_Fp(rows, ncol, p):
    M = [[x % p for x in r] for r in rows]
    nr = len(M)
    pivots = 0
    r = 0
    for c in range(ncol):
        piv = None
        for i in range(r, nr):
            if M[i][c] % p != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p-2, p)
        M[r] = [(x*inv) % p for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(a - f*b) % p for a,b in zip(M[i], M[r])]
        pivots += 1
        r += 1
        if r == nr: break
    return ncol - pivots

random.seed(444)
print("=== DOUBLE-BLOCK (twisted) c=1 clique constraint-space finrank ===")
print("matrix = [ ones ; gamma ], cols = |W| = w+1, expect nullity = w-1 (indep) / w (const gamma)")
ok_indep = ok_const = 0; tot_indep = tot_const = 0
for w in range(2, 8):          # |W| = w+1 = 3..8
    ncol = w + 1
    for trial in range(40):
        # branch (a): gamma with >=2 distinct values (random, force not-all-equal)
        gamma = [Fraction(random.randint(-9,9)) for _ in range(ncol)]
        if len(set(gamma)) == 1:
            gamma[0] += 1
        rowsQ = [[Fraction(1)]*ncol, gamma[:]]
        nQ = nullity_Q(rowsQ, ncol)
        gi = [int(x) for x in gamma]
        nFp = nullity_Fp([[1]*ncol, gi], ncol, 101)
        exp = (w+1) - 2   # = w-1
        tot_indep += 1
        if nQ == exp and nFp == exp: ok_indep += 1
        else: print(f"  INDEP MISMATCH w={w} nQ={nQ} nFp={nFp} exp={exp} gamma={gi}")

        # branch (b): gamma constant -> proportional to ones
        c = random.randint(-9,9)
        gconst = [Fraction(c)]*ncol
        nQc = nullity_Q([[Fraction(1)]*ncol, gconst[:]], ncol)
        nFpc = nullity_Fp([[1]*ncol, [c]*ncol], ncol, 101)
        expc = (w+1) - 1  # = w
        tot_const += 1
        if nQc == expc and nFpc == expc: ok_const += 1
        else: print(f"  CONST MISMATCH w={w} nQ={nQc} nFp={nFpc} exp={expc} c={c}")

print(f"INDEP (gamma >=2 distinct vals): {ok_indep}/{tot_indep} -> nullity = w-1")
print(f"CONST (gamma all equal):        {ok_const}/{tot_const} -> nullity = w  (collapses)")
print()
print("MECHANISM: the 2 x (w+1) matrix [ones; gamma] has rank 2 iff rows independent iff gamma not")
print("a scalar multiple of ones iff gamma non-constant. rank 2 -> nullity (w+1)-2 = w-1. rank 1")
print("(gamma const) -> nullity (w+1)-1 = w. So the twisted inf is dim w-1 EXACTLY under the honest")
print("independence hypothesis (gamma non-constant); WITHOUT it the inf is just the single hyperplane.")
