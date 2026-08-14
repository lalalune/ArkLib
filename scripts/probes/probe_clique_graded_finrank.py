#!/usr/bin/env python3
"""
PROBE (#444, Conj-41 clique GRADED c>=2 relation-module dimension).

The clique relation module (Round 21/22) is in bijection (single block) with
    V_single = { (v_alpha)_{alpha in W} : deg v_alpha < c-1, sum_alpha v_alpha = 0 }
and (double block, distinct gamma) with
    V_double = { (v_alpha) : deg v_alpha < c-1, sum v_alpha = 0, sum gamma_alpha v_alpha = 0 }.

Here each v_alpha is a polynomial of degree < c-1, i.e. a vector in F^{c-1}.
So a v-tuple is an element of (F^{c-1})^{w+1} = F^{(w+1)(c-1)}, and "sum v_alpha = 0" is a
COEFFICIENTWISE constraint: it imposes (c-1) scalar equations (one per coefficient slot), NOT 1.

CLAIMED PROSE NUMERALS (Conjecture41CliqueRelationModule docstring):
    dim V_single = (w+1)(c-1) - (c-1)         = w(c-1)
    dim V_double = (w+1)(c-1) - 2(c-1)        = (w-1)(c-1)    [distinct gamma => 2 indep blocks per slot]

This probe builds the EXACT constraint matrix over Q (Fraction) and over F_p and computes the
nullity by Gaussian elimination, for w=2..6, c=1..5, to confirm/refute the graded numerals.
"""
from fractions import Fraction
import random, itertools

def nullity_Q(rows, ncols):
    # rows: list of lists of Fraction, length ncols. nullity = ncols - rank.
    M = [r[:] for r in rows]
    rank = 0
    pivot_cols = []
    r = 0
    for c in range(ncols):
        # find pivot
        piv = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = M[r][c]
        M[r] = [x / inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f*b for a, b in zip(M[i], M[r])]
        r += 1
        rank += 1
        if r == len(M):
            break
    return ncols - rank

def nullity_Fp(rows, ncols, p):
    M = [[x % p for x in r] for r in rows]
    rank = 0; r = 0
    def inv(a): return pow(a, p-2, p)
    for c in range(ncols):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % p != 0:
                piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        iv = inv(M[r][c])
        M[r] = [(x*iv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(a - f*b) % p for a, b in zip(M[i], M[r])]
        r += 1; rank += 1
        if r == len(M): break
    return ncols - rank

def build_single(w, c):
    # variables: x[alpha][k], alpha in 0..w (w+1 of them), k in 0..c-2 (c-1 coeff slots)
    # if c==1: c-1 == 0 slots => no variables, no constraints => dim 0
    wp1 = w + 1
    slots = c - 1
    ncols = wp1 * slots
    rows = []
    # sum_alpha v_alpha = 0  coefficientwise: for each slot k, sum_alpha x[alpha][k] = 0
    for k in range(slots):
        row = [Fraction(0)] * ncols
        for a in range(wp1):
            row[a*slots + k] = Fraction(1)
        rows.append(row)
    return rows, ncols

def build_double(w, c, gammas):
    wp1 = w + 1
    slots = c - 1
    ncols = wp1 * slots
    rows = []
    for k in range(slots):
        row = [Fraction(0)] * ncols
        for a in range(wp1):
            row[a*slots + k] = Fraction(1)
        rows.append(row)
    for k in range(slots):
        row = [Fraction(0)] * ncols
        for a in range(wp1):
            row[a*slots + k] = Fraction(gammas[a])
        rows.append(row)
    return rows, ncols

print("=== SINGLE BLOCK: dim V_single  vs claimed w(c-1) ===")
ok_s = 0; tot_s = 0
for w in range(2, 7):
    for c in range(1, 6):
        rows, ncols = build_single(w, c)
        nul = nullity_Q(rows, ncols)
        claim = w*(c-1)
        tot_s += 1
        match = (nul == claim)
        ok_s += match
        if not match:
            print(f"  MISMATCH w={w} c={c}: nullity={nul} claim={claim}")
print(f"  single: {ok_s}/{tot_s} match w(c-1)")

print("=== DOUBLE BLOCK (distinct gamma): dim V_double vs claimed (w-1)(c-1) ===")
ok_d = 0; tot_d = 0; ok_d_fp = 0
for w in range(2, 7):
    for c in range(1, 6):
        for trial in range(20):
            # distinct gammas (so the 2 blocks are independent per slot)
            gammas = random.sample(range(1, 200), w+1)
            rows, ncols = build_double(w, c, gammas)
            nul = nullity_Q(rows, ncols)
            # distinct gamma + slots>=1 => rank of the 2*slots constraints is 2*slots (if w+1>=2)
            claim = (w-1)*(c-1)
            tot_d += 1
            ok_d += (nul == claim)
            # F_p check
            p = 101
            gammas_fp = random.sample(range(1, p), w+1)
            rows_fp = [[int(x) for x in r] for r in build_double(w, c, gammas_fp)[0]]
            nul_fp = nullity_Fp(rows_fp, ncols, p)
            ok_d_fp += (nul_fp == claim)
print(f"  double Q : {ok_d}/{tot_d} match (w-1)(c-1)")
print(f"  double Fp: {ok_d_fp}/{tot_d} match (w-1)(c-1)")
