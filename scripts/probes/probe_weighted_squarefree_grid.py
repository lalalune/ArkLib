#!/usr/bin/env python3
"""Probe for the WEIGHTED squarefree two-prime classification (grid form) — the
(a)-gate base case named after O96-O99: de Bruijn 1953 with N-multiplicities at
n = p*q, on the CRT grid.

TARGET:
  p != q primes, xi a primitive p-th root, eta a primitive q-th root (char 0),
  W : [0,p) x [0,q) -> N.
      Sum_{i<p, j<q} W[i][j] * xi^i * eta^j = 0
  IFF  W splits as a row+column function:  W[i][j] = alpha[i] + beta[j]
       with alpha, beta : N  (NONNEGATIVE — the positivity is the content).

Route under test (Lean plan):
  forward: K = Q(xi); the K-valued column sums A(j) = Sum_i W[i][j] xi^i are ALL
  EQUAL (slice_of_packet_minpoly at minpoly_K(eta) = Phi_q — CRTPacketMinpoly);
  equal columns + prime-level Q-rigidity (vanishing_combination_const) give the
  MODULAR EQUATION  W[i][j] + W[0][0] = W[i][0] + W[0][j];  the argmin shift
  produces NONNEGATIVE alpha, beta.  Converse: geometric sums kill both parts.

Checks (exit 0 iff all pass; exact integer arithmetic in Z[x,y]/(Phi_p, Phi_q)):
  G1  EXHAUSTIVE boxes: (p,q,B) = (2,3,3), (3,2,3), (2,5,2), (5,2,2), (3,5,1):
      vanishing family == row+column-decomposable family (set identity), and
      the modular equation holds on every vanishing W.
  G2  The constructive shift (alpha[i] = W[i][0]-min, beta[j] = W[argmin][j])
      reproduces W exactly on every vanishing W (the Lean witness recipe).
  G3  Controls: single-cell bumps of decomposable W never vanish; the all-ones
      W (= 1 + 0 split) vanishes; W = unit matrix does not.
"""

import sys
from itertools import product

FAIL = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAIL.append(name)


def vanishes(W, p, q):
    """Sum W[i][j] xi^i eta^j == 0 in Q(zeta_p, zeta_q), exact.

    Basis xi^i eta^j, 0<=i<p-1, 0<=j<q-1, reducing xi^(p-1) and eta^(q-1)."""
    M = [[0] * (q - 1) for _ in range(p - 1)]

    def add(i, j, c):
        if i == p - 1 and j == q - 1:
            for ii in range(p - 1):
                for jj in range(q - 1):
                    M[ii][jj] += c
        elif i == p - 1:
            for ii in range(p - 1):
                M[ii][j] -= c
        elif j == q - 1:
            for jj in range(q - 1):
                M[i][jj] -= c
        else:
            M[i][j] += c

    for i in range(p):
        for j in range(q):
            add(i, j, W[i][j])
    return all(all(c == 0 for c in row) for row in M)


def decomposable(W, p, q):
    """W[i][j] = alpha[i] + beta[j], alpha,beta >= 0, via the argmin shift."""
    i0 = min(range(p), key=lambda i: W[i][0])
    alpha = [W[i][0] - W[i0][0] for i in range(p)]
    beta = [W[i0][j] for j in range(q)]
    ok = all(W[i][j] == alpha[i] + beta[j] for i in range(p) for j in range(q))
    return ok and all(a >= 0 for a in alpha) and all(b >= 0 for b in beta)


def modular_eq(W, p, q):
    return all(W[i][j] + W[0][0] == W[i][0] + W[0][j]
               for i in range(p) for j in range(q))


def run(p, q, B):
    tot = nvan = bad_iff = bad_mod = bad_shift = 0
    cells = p * q
    for flat in product(range(B + 1), repeat=cells):
        W = [list(flat[i * q:(i + 1) * q]) for i in range(p)]
        v = vanishes(W, p, q)
        d = decomposable(W, p, q)
        tot += 1
        if v:
            nvan += 1
            if not modular_eq(W, p, q):
                bad_mod += 1
            if not d:
                bad_shift += 1
        if v != d:
            bad_iff += 1
    check(f"G1 iff exhaustive p={p} q={q} B={B}", bad_iff == 0,
          f"vanishing={nvan}/{tot}")
    check(f"G1 modular equation p={p} q={q}", bad_mod == 0)
    check(f"G2 argmin shift reproduces p={p} q={q}", bad_shift == 0)


def main():
    print("== WEIGHTED squarefree two-prime grid probe (falsify-first) ==\n")
    run(2, 3, 3)
    run(3, 2, 3)
    run(2, 5, 2)
    run(5, 2, 2)
    run(3, 5, 1)
    p, q = 3, 5
    ones = [[1] * q for _ in range(p)]
    check("G3 all-ones vanishes", vanishes(ones, p, q))
    unit = [[1 if (i, j) == (0, 0) else 0 for j in range(q)] for i in range(p)]
    check("G3 unit matrix does not vanish", not vanishes(unit, p, q))
    bump = [[1] * q for _ in range(p)]
    bump[1][2] += 1
    check("G3 bumped all-ones does not vanish", not vanishes(bump, p, q))
    if FAIL:
        print(f"FAILURES: {FAIL}")
        sys.exit(1)
    print("ALL CHECKS PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
