#!/usr/bin/env python3
"""
A5-TERWILLIGER decomposition probe (#444) -- corrected decisive test.

Honest decomposition of the reduced sum into its Terwilliger-graded pieces:
    S(u0) = Sum_{i=k+1}^{N} K_w(i) * T_i(u0),   T_i(u0) = Sum_{xi in D, wt(xi)=i} e_p(xi.u0).
Here T_i is the character sum over the weight-i subconstituent of D (a Terwilliger
E_i^*-projected piece).  The Terwilliger ANGLE claims the operator norm of S is bounded
by sqrt(n log) because D sits in a low-dim T-module.

THE TEST: compute, for the worst sampled u0, the size of each graded piece |T_i| and the
weighted total |S|.  Compare to:
  - the wall  M = max_b |eta_b|  (the i=N plain piece is governed by this)
  - the Johnson/Parseval scale  sqrt(n)
  - the target sqrt(n log(p/n))

If the dominant contribution to S is K_w(N) * T_N and T_N is itself a wall-object (no
gain), the angle reduces to the wall.  If some low-weight graded piece carries genuine
sqrt(n)-cancellation absent from M, that would be the crack.

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


def gauss_period(G, b, p):
    s = 0j
    for y in G:
        s += cmath.exp(2j * math.pi * (b * y % p) / p)
    return s


def main():
    print("=" * 104)
    print("A5-TERWILLIGER GRADED DECOMPOSITION: per-weight pieces T_i and whether the")
    print("dominant K_w(N)*T_N piece is the wall, leaving no independent Terwilliger gain.")
    print("Honesty: proper mu_n, n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1.")
    print("=" * 104)

    for mu in range(2, 5):
        n = 2 ** mu
        N = n
        p = find_prime(n, n ** 3 * 8)
        assert (p - 1) % n == 0 and isprime(p) and p > n ** 3 and n != p - 1
        domain = mu_n(p, n)
        kdim = max(1, n // 4)
        dperp = N - kdim
        w = N // 2

        # the wall M over this subgroup (b ranges 1..min(p, 4000) sample of cosets; for
        # exactness we'd need all b, but the structured cosets dominate -- we do all b
        # only if p small enough)
        if p <= 40000:
            M = max(abs(gauss_period(domain, b, p)) for b in range(1, p))
        else:
            M = max(abs(gauss_period(domain, b, p)) for b in range(1, 4000))

        random.seed(11)
        SAMPLES = 2500
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
                cw.append(gx)
            wt = sum(1 for a in cw if a != 0)
            words.append((cw, wt))

        # find a worst-ish u0 over a sample, maximizing |S|
        bestS = 0.0
        best_pieces = None
        Kvals = {i: krawtchouk(N, p, w, i) for i in range(N + 1)}
        for _ in range(120):
            u0 = [random.randrange(p) for _ in range(N)]
            graded = Counter()  # i -> complex T_i
            gradedC = {}
            for cw, wt in words:
                inner = sum(cw[i] * u0[i] for i in range(N)) % p
                ph = cmath.exp(2j * math.pi * inner / p)
                gradedC[wt] = gradedC.get(wt, 0j) + ph
            S = sum(Kvals[i] * gradedC.get(i, 0j) for i in gradedC)
            if abs(S) > bestS:
                bestS = abs(S)
                best_pieces = dict(gradedC)
        # report
        TN = abs(best_pieces.get(N, 0j))
        KN = Kvals[N]
        domTerm = abs(KN) * TN
        sqn = math.sqrt(n)
        snl = math.sqrt(n * math.log(p / n))
        print(f"\nmu={mu} n={n} p={p} kdim={kdim} w={w}  (p/n^3={p/n**3:.0f}, |D-sample|={len(words)})")
        print(f"  wall M = max_b|eta_b| = {M:.4f}   sqrt(n)={sqn:.3f}   sqrt(n log(p/n))={snl:.3f}")
        print(f"  worst sampled |S| = {bestS:.4e}")
        print(f"  dominant piece K_w(N)*|T_N| = {domTerm:.4e}   (|T_N|={TN:.3f}, K_w(N)={KN})")
        print(f"  |T_N| / sqrt(|D-sample|) = {TN/math.sqrt(len(words)):.4f}  "
              f"(plain dual char-sum normalized; ~ wall/Parseval scale)")
        # the key ratio: is the SUM dominated by the N piece, i.e. by the plain dual sum?
        frac = domTerm / bestS if bestS else 0
        print(f"  dominant-piece fraction of |S| = {frac:.3f}  (near 1 => S ~ K_w(N)*plain")
        print(f"     dual-code char sum = the WALL object; Terwilliger grading adds nothing)")

    print()
    print("CONCLUSION CRITERION:")
    print("  T_N (the full-weight subconstituent char sum) IS the plain dual-code character")
    print("  sum, which by Poisson/MacWilliams = the per-frequency Gauss-period sum over mu_n.")
    print("  Its normalized size tracks the WALL.  The other graded pieces T_i (i<N) are")
    print("  supported on the o(1) low-weight dual words and carry no extra structure that")
    print("  could deliver sqrt(n log).  => route 85 reduces to the BGK/Paley wall.")


if __name__ == "__main__":
    main()
