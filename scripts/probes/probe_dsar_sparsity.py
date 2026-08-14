#!/usr/bin/env python3
"""probe_dsar_sparsity.py  (#444, route: Bernstein-Markov-Turan on eta)

Object: eta_b = sum_{x in mu_n} e_p(b x), mu_n = 2-power mult subgroup, n = 2^mu.
Question: does the SPARSITY (n unit coeffs over [0,p)) bound M = max_b|eta_b| better than the
trivial n -- via a Turan / Bernstein-Markov inequality -- or does any improvement need the actual
support ARITHMETIC (= the BGK / Konyagin wall)?

Decisive measurement: an ARBITRARY n-sparse unit support (n consecutive frequencies) attains the
trivial value n at a nonzero frequency. So the subgroup M ~ sqrt(n log q) << n is a fact about
WHICH n frequencies (the multiplicative arithmetic), never about HOW MANY (the sparsity count).
=> sparsity count alone gives nothing below trivial n; the route reduces to BGK at log depth.
"""
import numpy as np, math
from sympy import isprime, primitive_root


def build_mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    S, x = [], 1
    for _ in range(n):
        S.append(x); x = x * h % p
    assert len(set(S)) == n
    return np.array(S)


def M_of(p, n):
    S = build_mu_n(p, n)
    best, chunk = 0.0, 200000
    for st in range(1, p, chunk):
        bb = np.arange(st, min(st + chunk, p))[:, None]
        ph = (bb * S[None, :]) % p
        best = max(best, np.abs(np.exp(2j * np.pi * ph / p).sum(axis=1)).max())
    return best


def arbitrary_consec_max(p, n):
    """Arbitrary n-sparse unit support = {0,1,...,n-1}; max over nonzero b."""
    S = np.arange(n)
    best = 0.0
    for b in range(1, min(p, 3 * p // n + 5)):
        ph = (b * S) % p
        best = max(best, abs(np.exp(2j * np.pi * ph / p).sum()))
    return best


if __name__ == "__main__":
    print("# eta_b = sum_{x in mu_n} e_p(bx). M=max_b|eta_b|. trivial sparsity ceiling = n.")
    for (p, n) in [(4129, 8), (65537, 16), (1048609, 32)]:
        assert isprime(p) and (p - 1) % n == 0
        M, arb, logq = M_of(p, n), arbitrary_consec_max(p, n), math.log(p / n)
        print(f"n={n:3d} p={p:8d} M={M:7.3f} M/sqrt(n)={M/math.sqrt(n):5.3f} "
              f"M/sqrt(n*logq)={M/math.sqrt(n*logq):5.3f} | "
              f"arbitrary-sparse(consec)max={arb:6.2f} (trivial n={n})", flush=True)
