"""
L1 / #407 part (2): FACTOR the obstruction integer D whose prime factors ARE the count-lane
bad primes, and measure the largest-prime-factor growth vs n.

THE OBSTRUCTION (from the completeness lemma, KB prize-407 doc):
A prime p == 1 mod n is "bad" (admits a spurious antipodal-free config with sum u == 0 and
sum u^3 == 0 mod p) only if a degree-1 prime 𝔭 | p divides alpha := sum_{u in U} u  in Z[zeta_n]
for some antipodal-free U.  So the bad primes are odd prime factors of the integers
    N(alpha) = N_{Q(zeta_n)/Q}( sum_{u in U} u )           (and jointly N(sum u^3))
ranging over antipodal-free U subset mu_n.

We compute  D_n := the set of distinct ODD prime factors p == 1 mod n appearing in any
N(sum_{u in U} u) for antipodal-free U  (this is the relevant odd part of the obstruction),
and report:
  - the FULL prime factorization landscape (is each N(alpha) = 2^a * small primes?),
  - the LARGEST odd bad prime as a function of n,
  - the GROWTH LAW of max bad prime vs n (compare to n^2, n^3, 2^n, n^{n/2}).

The genuine bad-prime test (sum u == 0 AND sum u^3 == 0 at the SAME embedding) is stricter;
but the NORM factors are the COMPLETE candidate set, so max(candidate) >= max(genuine bad).
We compute both: the candidate-prime growth (norm factors) and the genuine bad-prime growth.
"""
import itertools
from math import gcd
from sympy import factorint, primerange, isprime

# Work in Z[zeta_n] via the cyclotomic field. We use the power basis representation
# and the norm = product over Galois conjugates (sigma_a: zeta -> zeta^a, gcd(a,n)=1).
import cmath


def norm_of_rootsum(exps, n):
    """
    N_{Q(zeta_n)/Q}( sum_{j in exps} zeta_n^j )  as an exact integer, via resultant of the
    sum-polynomial with the n-th cyclotomic polynomial.  We compute it as the product over
    the phi(n) Galois conjugates sigma_a (a coprime to n): prod_a (sum_j zeta^{a j}),
    rounded to nearest integer (the norm is a rational integer).
    """
    import numpy as np
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    prod = 1.0 + 0.0j
    zeta = cmath.exp(2j * cmath.pi / n)
    for a in units:
        s = sum(zeta ** ((a * j) % n) for j in exps)
        prod *= s
    val = prod.real
    return round(val)


def antipodal_free_subsets(n, sizes):
    HALF = n // 2
    for size in sizes:
        for S in itertools.combinations(range(n), size):
            Sset = set(S)
            if any(((j + HALF) % n) in Sset for j in S):
                continue
            # also drop the trivial all-equal / sum-zero-over-Z cases handled by norm
            yield S


def candidate_bad_primes(n, sizes):
    """Distinct odd primes p == 1 mod n dividing some N(sum_{u in U} u), antipodal-free U."""
    primes_split = set()
    all_norm_factors = {}
    norms = []
    for S in antipodal_free_subsets(n, sizes):
        N1 = norm_of_rootsum(S, n)
        norms.append((S, N1))
        if N1 == 0:
            continue
        for p, e in factorint(abs(N1)).items():
            all_norm_factors[p] = all_norm_factors.get(p, 0) + e
            if p % n == 1 and p != 2:
                primes_split.add(p)
    return primes_split, all_norm_factors, norms


def genuine_bad_primes(n, sizes, hi):
    """Primes p == 1 mod n where a GENUINE spurious config exists (sum u == sum u^3 == 0 mod p)."""
    bad = []
    for p in primerange(n + 1, hi):
        if p % n != 1:
            continue
        e = (p - 1) // n
        HALF = n // 2
        g = None
        for a in range(2, p):
            gg = pow(a, e, p)
            if pow(gg, n, p) == 1 and pow(gg, HALF, p) == p - 1:
                g = gg
                break
        if g is None:
            continue
        found = False
        for S in antipodal_free_subsets(n, sizes):
            us = [pow(g, j, p) for j in S]
            if sum(us) % p != 0:
                continue
            if sum(pow(u, 3, p) for u in us) % p != 0:
                continue
            found = True
            break
        if found:
            bad.append(p)
    return bad


if __name__ == "__main__":
    import math
    print("L1 part (2): obstruction-norm factorization & bad-prime growth law\n")
    for n, sizes in [(8, [3, 4]), (16, [4, 6]), (32, [4])]:
        cand, factors, norms = candidate_bad_primes(n, sizes)
        # show the structure of the norms: are they 2^a * small?
        sample = sorted(set(abs(N) for _, N in norms if N != 0))[:12]
        # max prime factor over all norms
        maxpf = 1
        for _, N in norms:
            if N != 0:
                for p in factorint(abs(N)):
                    maxpf = max(maxpf, p)
        cand_sorted = sorted(cand)
        print(f"n={n}: #antipodal-free subsets considered={sum(1 for _ in antipodal_free_subsets(n,sizes))}")
        print(f"   distinct |N(sum u)| values (sample): {sample}")
        print(f"   ALL prime factors of the norms (p:total_exp): "
              f"{dict(sorted(factors.items())[:15])}")
        print(f"   LARGEST prime factor of any N(sum u): {maxpf}")
        print(f"   candidate odd bad primes (p == 1 mod {n}): {cand_sorted}")
        if cand_sorted:
            mx = max(cand_sorted)
            print(f"   max candidate bad prime = {mx}  "
                  f"(n^2={n**2}, n^3={n**3}, n^3.5={int(n**3.5)})")
    print()
    print("=== genuine bad primes (sum u == sum u^3 == 0 at SAME embedding) ===")
    for n, sizes, hi in [(8, [3, 4], 5000), (16, [4, 6], 8000), (32, [4, 6], 3000)]:
        gb = genuine_bad_primes(n, sizes, hi)
        if gb:
            mx = max(gb)
            print(f"n={n}: genuine bad primes (<{hi}) = {gb}; max={mx}, "
                  f"ratio max/n^3 = {mx/n**3:.3f}, max/n^2 = {mx/n**2:.3f}")
        else:
            print(f"n={n}: no genuine bad prime < {hi}")
