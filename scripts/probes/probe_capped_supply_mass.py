#!/usr/bin/env python3
"""Capped-supply mass identity + floor probe (issue #389).

THE MASS IDENTITY (CappedSupplyMassIdentity.lean, machine-checked):
  Sum_w Sum_{c : t<=a_c<=cap} C(a_c, t)
    = #code * Sum_{j=t}^{cap} C(n,j) * (q-1)^(n-j) * C(j,t).
Mean capped supply over the word space = that, divided by q^n.

This probe:
  1. Verifies the identity by brute force over all q^n words for small (q,n,k).
  2. Tabulates the mean and the pigeonhole floor B >= mean for production-shaped
     parameters, showing it equals the witness mass C(n,t)/q^(m+1) up to the
     (1-1/q)^(n-t) ~ e^(-(n-t)/q) factor.

Key consequence: any admissible B for ExplainableCoreSupply dom k m B is
>= mean_supply -- the witness-mass FLOOR is unconditional. The open question is
only whether ADVERSARIAL concentration pushes the max polynomially above this mean.
"""
from math import comb, prod
from itertools import product


def code_size(q, k):
    return q ** k  # |{deg < k polynomials}| over F_q


def mean_supply(q, n, k, t, cap):
    total = code_size(q, k) * sum(
        comb(n, j) * (q - 1) ** (n - j) * comb(j, t)
        for j in range(t, cap + 1)
    )
    return total / q ** n


def witness_mass(q, n, k, m):
    t = k + m + 1
    return comb(n, t) / q ** (m + 1)


def brute_force_identity(q, n, k, t, cap):
    """Sum over all words of the capped supply; compare to the closed form.

    Domain = first n elements of F_q (identity); codewords = degree-<k polys
    evaluated, i.e. all q^k coefficient tuples (a_0,...,a_{k-1})."""
    dom = list(range(n))
    # enumerate codewords as coefficient tuples
    codewords = []
    for coeffs in product(range(q), repeat=k):
        cw = [sum(coeffs[d] * (x ** d) for d in range(k)) % q for x in dom]
        codewords.append(cw)
    total = 0
    for w in product(range(q), repeat=n):
        for cw in codewords:
            a = sum(1 for i in range(n) if cw[i] == w[i])
            if t <= a <= cap:
                total += comb(a, t)
    closed = code_size(q, k) * sum(
        comb(n, j) * (q - 1) ** (n - j) * comb(j, t)
        for j in range(t, cap + 1)
    )
    return total, closed


if __name__ == "__main__":
    print("== identity verification (brute force over all q^n words) ==")
    for (q, n, k, t, cap) in [(3, 3, 2, 2, 3), (3, 4, 2, 2, 3), (5, 3, 2, 2, 3),
                              (2, 5, 2, 3, 4)]:
        got, want = brute_force_identity(q, n, k, t, cap)
        ok = "OK" if got == want else "MISMATCH"
        print(f"  q={q} n={n} k={k} t={t} cap={cap}: "
              f"brute={got} closed={want}  [{ok}]")

    print("\n== mean supply vs witness mass (production-shaped, m=1, k=2) ==")
    print(f"  {'q':>4} {'n':>4} {'t':>3} {'mean_supply':>14} "
          f"{'witness_mass':>14} {'ratio':>7}")
    for (q, n) in [(17, 17), (31, 31), (101, 101), (131, 128), (257, 256)]:
        k, m = 2, 1
        t = k + m + 1
        # full-support cap = n (count all codewords agreeing on >= t)
        ms = mean_supply(q, n, k, t, n)
        wm = witness_mass(q, n, k, m)
        print(f"  {q:>4} {n:>4} {t:>3} {ms:>14.3f} {wm:>14.3f} "
              f"{ms / wm:>7.3f}")
    print("\n  ratio -> (1-1/q)^(n-t) ~ e^(-(n-t)/q): at q~n a constant ~ e^-1,")
    print("  so the floor B >= mean is Theta(C(n,t)/q^(m+1)) = Theta(witness mass).")
