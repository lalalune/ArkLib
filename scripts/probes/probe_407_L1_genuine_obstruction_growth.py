"""
L1 / #407 part (2+3): the GENUINE obstruction integer for the count-lane, and its growth law.

The bad primes are where a GENUINE spurious antipodal-free config U appears: an embedding
(a degree-1 prime 𝔭 | p) at which BOTH sum_{u in U} u == 0 AND sum_{u in U} u^3 == 0.
At such an embedding zeta_n -> g (a primitive n-th root in F_p), so 𝔭 | gcd_in_Z[zeta](
   sum_{u} u ,  sum_{u} u^3 ) ... but gcd of ideals is the issue.  The clean integer
whose prime factors are EXACTLY the genuine bad primes is the RESULTANT of the two
single-variable integer polynomials obtained by eliminating: for a fixed exponent set U,
let alpha = sum zeta^{u}, beta = sum zeta^{3u} in Z[zeta_n]; a genuine bad prime is one
where alpha and beta share a degree-1 prime above p, i.e. p | Res_{x}(minpoly(alpha), minpoly(beta))
is necessary but not sufficient (different conjugates).  Cleanest exact criterion (used here):
the genuine bad primes for U are the primes p == 1 mod n such that the IDEAL (alpha, beta, p)
has a degree-1 factor -- equivalently, exists g primitive n-th root in F_p with both sums 0.

We compute the genuine bad set DIRECTLY (over F_p) for n=8..128 and fit the max-bad-prime
growth law, and SEPARATELY factor the single-condition norm N(alpha) to track candidate growth.

Goal: measure whether genuine-bad-prime(n) and candidate-prime(n) grow like poly(n) (and which power).
"""
import itertools
from math import gcd, log
from sympy import primerange, factorint
import cmath


def primitive_root_mod(p, n):
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    HALF = n // 2
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, HALF, p) == p - 1:
            return g
    return None


def antipodal_free(n, sizes):
    HALF = n // 2
    for size in sizes:
        for S in itertools.combinations(range(n), size):
            Sset = set(S)
            if any(((j + HALF) % n) in Sset for j in S):
                continue
            yield S


def genuine_bad_max(n, sizes, hi):
    """Max prime p == 1 mod n < hi with a genuine spurious antipodal-free config; list them."""
    bad = []
    for p in primerange(n + 1, hi):
        if p % n != 1:
            continue
        g = primitive_root_mod(p, n)
        if g is None:
            continue
        for S in antipodal_free(n, sizes):
            us = [pow(g, j, p) for j in S]
            if sum(us) % p != 0:
                continue
            if sum(pow(u, 3, p) for u in us) % p != 0:
                continue
            bad.append(p)
            break
    return bad


def norm_of_rootsum(exps, n, power=1):
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    prod = 1.0 + 0.0j
    zeta = cmath.exp(2j * cmath.pi / n)
    for a in units:
        s = sum(zeta ** ((a * power * j) % n) for j in exps)
        prod *= s
    return round(prod.real)


def candidate_max(n, sizes):
    """Max odd prime p == 1 mod n dividing some N(sum u) (single condition)."""
    primes = set()
    for S in antipodal_free(n, sizes):
        N1 = norm_of_rootsum(S, n)
        if N1 == 0:
            continue
        for p in factorint(abs(N1)):
            if p != 2 and p % n == 1:
                primes.add(p)
    return sorted(primes)


if __name__ == "__main__":
    print("GENUINE bad primes (both sum u=0 and sum u^3=0 at same embedding) and growth:\n")
    # genuine: keep sizes small for tractability (the minimal spurious configs are size 4-8)
    data_genuine = []
    for n, sizes, hi in [(8, [3, 4], 20000), (16, [4, 6], 40000), (32, [4, 6], 20000),
                         (64, [4], 70000), (128, [4], 200000)]:
        bad = genuine_bad_max(n, sizes, hi)
        mx = max(bad) if bad else 0
        data_genuine.append((n, mx, bad))
        if bad:
            print(f"n={n:4d}: genuine bad = {bad[:12]}{'...' if len(bad)>12 else ''} "
                  f"(scan<{hi}); MAX={mx}; max/n^2={mx/n**2:.2f} max/n^3={mx/n**3:.3f} "
                  f"log_n(max)={log(mx)/log(n):.2f}")
        else:
            print(f"n={n:4d}: NO genuine bad prime < {hi}")
    print()
    print("CANDIDATE primes (single condition, norm factors) and growth:\n")
    for n, sizes in [(8, [3, 4]), (16, [4, 6]), (32, [4, 6]), (64, [4])]:
        cand = candidate_max(n, sizes)
        if cand:
            mx = max(cand)
            print(f"n={n:4d}: #candidate odd primes={len(cand)}; MAX={mx}; "
                  f"log_n(max)={log(mx)/log(n):.2f} (n^3={n**3})")
    print()
    print("=== growth-law fit (genuine bad-prime exponent log_n(max)) ===")
    pts = [(n, mx) for n, mx, _ in data_genuine if mx > 0]
    for n, mx in pts:
        print(f"  n={n}: log_n(max_genuine_bad) = {log(mx)/log(n):.3f}")
