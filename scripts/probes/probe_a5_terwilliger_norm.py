#!/usr/bin/env python3
"""
A5-TERWILLIGER norm-collapse probe (#444) -- THE DECISIVE TEST.

We directly test whether the Terwilliger-module operator norm of the Krawtchouk-weighted
action equals M(mu_n) (the wall), or gives an independent smaller bound.

SETUP. The reduced sum S(u0) = Sum_{xi in D} K_w(wt xi) e_p(xi . u0) is a linear
functional of the additive character vector chi_{u0}. As u0 ranges over u1^perp, the
worst-case |S| is the OPERATOR NORM of the map
    u0  |->  S(u0)
restricted to the relevant subspace.  Equivalently |S| <= ||W|| where W is the
"weighted dual-code" vector  W = Sum_{xi in D} K_w(wt xi) delta_xi  in C[F_p^N], measured
against the character basis. The Terwilliger angle asks: is W confined to a low-dim
T-module so ||W (acting)|| << |Ball|?

We compute, over PROPER mu_n (n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1):

  (1) M = max_{b!=0} |eta_b|              (the wall)
  (2) Kbar = K_w(N)                       (the dominant Krawtchouk weight, =wt N is generic)
  (3) the FRACTION of D-mass at weight N  (=> K_w weighting is ~ constant scalar)
  (4) the explicit collapse identity:
        S(u0) = Kbar * (plain char sum over D)  +  Delta,
      |Delta| <= (low-weight mass) * max|K_w|, and the plain char sum over D is governed
      by eta_b.  We verify numerically that |S| / (Kbar) tracks the plain-char-sum norm,
      i.e. the Terwilliger weighting provides NO independent cancellation.

Honesty: proper mu_n, n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1.
"""
import math
import cmath
from collections import Counter
import sympy
from sympy import isprime
import numpy as np
import random


def find_prime(n, mult_lower):
    base = ((mult_lower // n) + 1) * n + 1
    p = base
    while True:
        if isprime(p):
            return p
        p += n


def primitive_root_of_order(p, n):
    g = sympy.primitive_root(p)
    return pow(g, (p - 1) // n, p)


def mu_n(p, n):
    w = primitive_root_of_order(p, n)
    return [pow(w, i, p) for i in range(n)]


def krawtchouk(N, q, k, i):
    s = 0
    for j in range(0, k + 1):
        s += ((-1) ** j) * ((q - 1) ** (k - j)) * math.comb(i, j) * math.comb(N - i, k - j)
    return s


def main():
    print("=" * 100)
    print("A5-TERWILLIGER NORM-COLLAPSE: does the Krawtchouk weighting give cancellation")
    print("beyond the plain character sum over D, or collapse to a CONSTANT scalar Kbar")
    print("times the plain sum (=> reduces to the wall M(mu_n))?")
    print("Honesty: proper mu_n, n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1.")
    print("=" * 100)
    print(f"{'mu':>3} {'n':>4} {'p':>9} {'wtN_frac':>9} {'|S|/sumD':>10} {'Kbar':>14} "
          f"{'ratio_vs_Kbar':>14}")

    for mu in range(2, 5):
        n = 2 ** mu
        N = n  # RS length = domain size
        p = find_prime(n, n ** 3 * 8)
        assert (p - 1) % n == 0 and isprime(p) and p > n ** 3 and n != p - 1
        domain = mu_n(p, n)
        kdim = max(1, n // 4)
        dperp = N - kdim
        w = N // 2  # window radius for Krawtchouk

        # dual weights v_x (nonzero) -- weight = #nonzero coords (v_x scaling irrelevant)
        # enumerate / sample dual codewords g of deg < dperp; record (codeword, weight)
        random.seed(7)
        SAMPLES = 1500
        words = []
        for _ in range(SAMPLES):
            deg = random.randint(0, dperp - 1)
            coeffs = [random.randrange(p) for _ in range(deg + 1)]
            if all(c == 0 for c in coeffs):
                coeffs = [1]
            cw = []
            for x in domain:
                gx = 0
                xp = 1
                for c in coeffs:
                    gx = (gx + c * xp) % p
                    xp = (xp * x) % p
                cw.append(gx)  # use g(x); v_x is a fixed nonzero per-coord scalar
            wt = sum(1 for a in cw if a != 0)
            words.append((tuple(cw), wt))

        wtN_frac = sum(1 for _, wt in words if wt == N) / len(words)
        Kbar = krawtchouk(N, p, w, N)  # dominant weight

        # Pick a worst-ish u0: scan a sample of u0 in F_p^N and measure
        #   S(u0)  = sum_xi K_w(wt xi) e_p(<xi,u0>)
        #   PlainD = sum_xi e_p(<xi,u0>)
        # Report max over sampled u0 of |S|, and |S|/|PlainD| -> should ~ Kbar if collapse.
        best_ratio = 0.0
        best_absS_over_sumD = 0.0
        sum_abs_ratio = 0.0
        cnt_ratio = 0
        for _ in range(60):
            u0 = [random.randrange(p) for _ in range(N)]
            S = 0j
            PlainD = 0j
            for cw, wt in words:
                inner = sum(cw[i] * u0[i] for i in range(N)) % p
                ph = cmath.exp(2j * math.pi * inner / p)
                Kw = krawtchouk(N, p, w, wt)
                S += Kw * ph
                PlainD += ph
            if abs(PlainD) > 1e-6:
                r = abs(S) / abs(PlainD)
                sum_abs_ratio += r
                cnt_ratio += 1
                best_ratio = max(best_ratio, r)
            best_absS_over_sumD = max(best_absS_over_sumD, abs(S) / len(words))
        avg_ratio = sum_abs_ratio / max(cnt_ratio, 1)
        print(f"{mu:>3} {n:>4} {p:>9} {wtN_frac:>9.4f} {best_absS_over_sumD:>10.3f} "
              f"{Kbar:>14d} {avg_ratio/abs(Kbar) if Kbar else 0:>14.4f}")

    print()
    print("READING:")
    print(" - wtN_frac near 1.0  => almost all D-words have full weight N, so K_w(wt xi) is")
    print("   the CONSTANT Kbar = K_w(N) on (1 - o(1)) of D.  The Krawtchouk weight does NOT")
    print("   vary across the module => it is a SCALAR, not a nontrivial operator.")
    print(" - ratio_vs_Kbar near 1.0 => |S(u0)| = Kbar * |plain char sum over D| up to lower")
    print("   order.  The plain char sum over D is, by MacWilliams/Poisson, governed by the")
    print("   per-frequency Gauss period eta_b over mu_n.  HENCE the Terwilliger-module norm")
    print("   REDUCES to the wall M(mu_n): no relocation of the cancellation locus occurs.")


if __name__ == "__main__":
    main()
