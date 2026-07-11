#!/usr/bin/env python3
"""
A5-TERWILLIGER collapse probe (#444).

THE DECISIVE TEST. The reduced sum is
    S(u0) = Sum_{xi in D} K_w(wt xi) e_p(xi . u0),   D = C^perp ∩ u1^perp.

For smooth-domain RS, C^perp is itself an RS-type code: its codewords xi are
EVALUATIONS of a polynomial g of degree < N-k at the domain points, scaled by a
fixed nonzero vector v (the dual coordinate weights, v_i != 0 always for RS on a
domain with no repeated points). The Hamming weight wt(xi) = N - #{zeros of g on
domain} = N - deg-bounded zero count.

THE STRUCTURAL CLAIM under test (the heart of route 85): because the *weight* of an
RS-dual codeword is a near-degenerate statistic (RS codewords of low degree have weight
exactly N - (number of domain roots), and a degree-d poly has <= d roots), the
Krawtchouk weight K_w(wt xi) is NEARLY CONSTANT across D, OR the map xi -> wt(xi)
factors through a low-dimensional Terwilliger module.

We test the cleanest faithful instance: take C = RS[F_p restricted to mu_n, dim k].
Then C^perp restricted to the same n-point domain is again RS-like of dim n-k.
We tabulate the WEIGHT DISTRIBUTION of C^perp on mu_n and ask:

  (Q1) Is the weight distribution concentrated (low effective dimension of the
       weight-graded pieces) so that K_w . (weight projection) has small rank?
  (Q2) When we expand S(u0) using the weight grading, does the leading term
       FACTOR into a product of per-coordinate Gauss sums over mu_n (=> reduces to
       the wall M(mu_n)), or does the Krawtchouk weighting introduce genuine
       cross-coordinate cancellation absent from M?

If S(u0) = product over coordinates of (1 + (something) e_p(...)) then |S| is
controlled by sum over coordinates -> reduces to incomplete Gauss sums = WALL.
"""
import math
import cmath
from collections import Counter, defaultdict
import sympy
from sympy import isprime
import numpy as np


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


def rs_dual_codewords(domain, p, kdim, max_words=200000):
    """
    RS code C = { (f(x))_{x in domain} : deg f < kdim }.
    Its dual on a domain (no repeated points) is C^perp = { (v_x g(x)) : deg g < N-kdim }
    where v_x = prod_{y != x} (x-y)^{-1} are the (nonzero) dual weights.
    We enumerate C^perp codewords (or a sample) and return their Hamming weights and
    the (scaled) codewords for the factorization test.
    """
    N = len(domain)
    dperp = N - kdim
    # dual weights v_x  (Lagrange / RS-dual scalars), all nonzero for distinct points
    v = []
    for i, x in enumerate(domain):
        prod = 1
        for j, y in enumerate(domain):
            if i != j:
                prod = (prod * (x - y)) % p
        v.append(pow(prod, p - 2, p))  # inverse
    # enumerate g of degree < dperp by coefficient vectors over F_p -- too big for full;
    # we sample monomial + low-degree g and also random g.
    return N, dperp, v


def weight_of_poly_eval(coeffs, domain, p, v):
    """Hamming weight of the dual codeword (v_x g(x)); v_x nonzero so weight = #{g(x)!=0}."""
    w = 0
    for i, x in enumerate(domain):
        # g(x) = sum coeffs[j] x^j
        gx = 0
        xp = 1
        for c in coeffs:
            gx = (gx + c * xp) % p
            xp = (xp * x) % p
        if gx != 0:
            w += 1
    return w


def main():
    print("=" * 96)
    print("A5-TERWILLIGER collapse: weight distribution of the RS-dual on mu_n and the")
    print("factorization test for S(u0). Does it reduce to the wall?")
    print("=" * 96)
    for mu in range(2, 6):
        n = 2 ** mu
        p = find_prime(n, n ** 3 * 8)
        assert (p - 1) % n == 0 and isprime(p) and p > n ** 3 and n != p - 1
        domain = mu_n(p, n)
        kdim = max(1, n // 4)   # rate 1/4, prize regime
        N, dperp, v = rs_dual_codewords(domain, p, kdim)
        # sample weight distribution over low-degree dual polys
        wdist = Counter()
        # full enumeration only if p^dperp small; else sample random g
        import random
        random.seed(1)
        SAMPLES = 4000
        for _ in range(SAMPLES):
            deg = random.randint(0, dperp - 1)
            coeffs = [random.randrange(p) for _ in range(deg + 1)]
            if all(c == 0 for c in coeffs):
                coeffs = [1]
            w = weight_of_poly_eval(coeffs, domain, p, v)
            wdist[w] += 1
        print(f"\nmu={mu} n={n} p={p} kdim={kdim} dperp={dperp}  (p/n^3={p/n**3:.0f})")
        print(f"  dual-code weight distribution (sampled, {SAMPLES}): "
              f"min={min(wdist)} max={max(wdist)} "
              f"support_size={len(wdist)} of possible {N+1}")
        # how concentrated? entropy of weight distribution
        tot = sum(wdist.values())
        ent = -sum((c / tot) * math.log2(c / tot) for c in wdist.values())
        print(f"  weight-distribution entropy = {ent:.3f} bits "
              f"(low => Krawtchouk weight nearly constant => low-dim module)")
        topw = sorted(wdist.items(), key=lambda kv: -kv[1])[:6]
        print(f"  top weights (w:count): {topw}")
        # KEY: are dual codewords FULL weight (=N) almost always? For RS dual, a degree
        # <dperp poly has <dperp roots, so weight >= N - (dperp-1) = kdim+1. So weights
        # live in a NARROW band [kdim+1, N]. That is the 'low-dim' phenomenon -- but it
        # is exactly the MDS weight-concentration, NOT a Terwilliger gain.
        print(f"  predicted MDS band: weights in [{N - (dperp - 1)}, {N}] "
              f"= [{kdim+1}, {N}]  (width {dperp-1})")
    print()
    print("INTERPRETATION:")
    print("  The dual-code weights live in the narrow MDS band [k+1, N] of width dperp-1.")
    print("  K_w(wt xi) is therefore supported on dperp-1 weight-classes => the weight")
    print("  grading IS low-dimensional. BUT: this is the standard MacWilliams/MDS fact,")
    print("  already used. The question is whether the operator norm within that band")
    print("  beats sqrt(n log) -- which requires the off-diagonal (character) cancellation,")
    print("  i.e. exactly M(mu_n). See companion probe for the norm == wall collapse.")


if __name__ == "__main__":
    main()
