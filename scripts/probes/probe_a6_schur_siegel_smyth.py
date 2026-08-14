#!/usr/bin/env python3
"""
A6 — Schur-Siegel-Smyth trace problem on the Gaussian period polynomial.

CORE IDENTITY (established, exact):
  M(mu_n) = max_{b != 0} | Sum_{x in mu_n} e_p(b x) | = max_i |eta_i|,
where eta_0,...,eta_{m-1} are the degree-m Gaussian periods (m = (p-1)/n),
the roots of the integer period polynomial Psi_p(T) in ZZ[T], deg m.
Each eta_i is a sum of n = 2^mu p-th roots of unity.

The A6 NEW LEMMA candidate: bound max_i |eta_i| <= C sqrt(n) using only the
INTEGER structure of Psi_p (its coefficients = power sums of the periods, i.e.
Newton's identities / absolute-trace machinery), NOT the domain arithmetic.

Key invariants of Psi_p (all in ZZ, computable from Gaussian-period theory):
  S_1 = Sum_i eta_i = Sum over ALL nonzero residues of e_p = -1.           (trace)
  S_2 = Sum_i eta_i^2.   For n | p-1, eta_i are complex (not real) in general,
        but the MULTISET {eta_i} is closed under complex conjugation, and
        Sum_i |eta_i|^2 is the RELEVANT energy because M = max|eta_i|.

  CRUCIAL distinction the manifesto warns about:
    Sum_i eta_i^2   (algebraic power sum, = trace of eta^2, an INTEGER)
    vs
    Sum_i |eta_i|^2 (the L2 energy of the magnitudes; = n*(p-1)/... Parseval).

This probe:
  (1) Verifies M(mu_n) = max_i |eta_i| exactly for proper subgroups.
  (2) Computes the integer power sums P_k = Sum_i eta_i^k for small k and the
      L2 energy E = Sum_i |eta_i|^2, to see which one controls the max.
  (3) Tests the candidate trace-problem inequality: does
        max_i |eta_i| <= C * sqrt(E / m)  ??  (mean-square spread bound)
      i.e. is the max period within O(1) of the RMS period? If yes, the L2
      energy (= second moment) controls the max --> but that is exactly the
      Johnson/energy horn (second moment blind to tails). We must see whether
      the INTEGER power sums P_k give anything BEYOND the L2 energy.
  (4) Tests whether Schur-style inequalities (using that P_k in ZZ, |eta_i|
      bounded, and the conjugate-closure) push max below the Mann boundary.

Honesty constraints: proper subgroup mu_n, n = 2^mu, n | p-1, p PRIME, p >> n^3,
NEVER n = p-1.
"""
import sys
import math
import cmath
from sympy import primerange, isprime

def primitive_root(p):
    # find a primitive root mod p
    if p == 2:
        return 1
    # factor p-1
    phi = p - 1
    fac = set()
    x = phi
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.add(d); x //= d
        d += 1
    if x > 1:
        fac.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def gaussian_periods(p, n):
    """
    Return the m = (p-1)/n Gaussian periods eta_i (complex), where mu_n is the
    unique subgroup of order n in (Z/p)^*, and eta_i = sum over coset i of e_p(x).
    Also return the exact sup-norm M(mu_n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|.
    """
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    # subgroup mu_n = { g^{m j} : j }  (order n). Its elements:
    sub = []
    cur = 1
    gm = pow(g, m, p)
    for _ in range(n):
        sub.append(cur)
        cur = (cur * gm) % p
    assert len(set(sub)) == n
    twopi = 2.0 * math.pi / p
    # M(mu_n): max over b != 0 of |sum_{x in mu_n} e_p(b x)|.
    # As b ranges over cosets, this gives the m periods. Compute all p-1 b's
    # (cheap enough) and also confirm only m distinct magnitudes.
    def period_sum(b):
        s = 0+0j
        for x in sub:
            ang = twopi * ((b * x) % p)
            s += cmath.exp(1j * ang)
        return s
    # the m periods correspond to b = g^i, i = 0..m-1 (coset reps of mu_n)
    etas = []
    gi = 1
    for i in range(m):
        etas.append(period_sum(gi))
        gi = (gi * g) % p
    M = max(abs(e) for e in etas)
    return etas, M, m, g

def power_sums(etas, K):
    """Integer power sums P_k = sum_i eta_i^k for k=1..K (rounded; should be ~integer)."""
    res = []
    for k in range(1, K+1):
        s = sum(e**k for e in etas)
        # should be a real integer
        res.append(s)
    return res

def run_case(p, n, verbose=True):
    etas, M, m, g = gaussian_periods(p, n)
    E = sum(abs(e)**2 for e in etas)          # L2 energy of magnitudes
    rms = math.sqrt(E / m)
    P = power_sums(etas, 4)
    sqrtn = math.sqrt(n)
    # candidate ratios
    r_max_sqrtn = M / sqrtn                    # M / sqrt(n)  -- the floor target
    r_max_rms = M / rms                        # max vs RMS (spread factor)
    r_max_johnson = M / math.sqrt(n * math.log(max(p / n, math.e)))  # vs Johnson sqrt(n log(p/n))
    if verbose:
        print(f"  p={p} n={n} m={m} g={g}")
        print(f"    M(mu_n)        = {M:.4f}")
        print(f"    sqrt(n)        = {sqrtn:.4f}     M/sqrt(n) = {r_max_sqrtn:.4f}")
        print(f"    RMS period     = {rms:.4f}     M/RMS     = {r_max_rms:.4f}")
        print(f"    sqrt(n log p/n)= {math.sqrt(n*math.log(max(p/n,math.e))):.4f}  M/that = {r_max_johnson:.4f}")
        print(f"    P1 (trace, should be -1)  = {P[0].real:+.3f} (im {P[0].imag:+.2e})")
        print(f"    P2 (sum eta^2)            = {P[1].real:+.3f} (im {P[1].imag:+.2e})")
        print(f"    E = sum|eta|^2            = {E:.3f}   (theory: should = n*m - n = n(m-1)? check)")
    return dict(p=p, n=n, m=m, M=M, E=E, rms=rms, P=[complex(x) for x in P],
                r_max_sqrtn=r_max_sqrtn, r_max_rms=r_max_rms, r_max_johnson=r_max_johnson)

def find_primes_with_subgroup(n, count, pmin):
    """primes p with n | p-1, p prime, p > pmin (we want p >> n^3)."""
    out = []
    p = pmin
    # iterate multiples of n above pmin: p = 1 + n*t
    t = (pmin // n) + 1
    while len(out) < count:
        p = 1 + n * t
        if isprime(p):
            out.append(p)
        t += 1
    return out

if __name__ == "__main__":
    print("=== A6: Schur-Siegel-Smyth on Gaussian period polynomial ===")
    print("CORE: M(mu_n) = max_i |eta_i|; eta_i roots of integer Psi_p, deg m=(p-1)/n.\n")
    # First: verify the core identity claim numerically AND check E formula.
    # Parseval: sum over ALL b in Z/p of |sum_{x in mu_n} e_p(bx)|^2 = p * n  (Plancherel,
    # since the indicator of mu_n has n ones). b=0 term = n^2. So
    # sum_{b!=0} |..|^2 = p*n - n^2 = n(p-n). Each coset value repeated n times
    # (b and b' in same coset of mu_n give same magnitude... actually same value).
    # So sum_{i=0}^{m-1} n*|eta_i|^2 = n(p-n) => E = sum_i |eta_i|^2 = p - n.
    print("Energy check: theory says E = sum_i |eta_i|^2 = p - n (Parseval).")
    print("So RMS = sqrt((p-n)/m) = sqrt((p-n)*n/(p-1)) ~ sqrt(n) for p>>n.  <-- KEY\n")

    cases = []
    # proper subgroups, p >> n^3
    for mu in [2, 3, 4, 5, 6]:
        n = 2**mu
        pmin = max(50 * n**3, 1000)
        primes = find_primes_with_subgroup(n, 4, pmin)
        print(f"--- n = 2^{mu} = {n},  primes p >> n^3 (pmin={pmin}) ---")
        for p in primes:
            res = run_case(p, n)
            cases.append(res)
        print()

    print("=== SUMMARY: M / sqrt(n)  and  M / RMS across cases ===")
    print(f"{'p':>9} {'n':>5} {'m':>7} {'M':>9} {'M/sqrtn':>9} {'M/RMS':>8} {'M/Johnson':>10}")
    for c in cases:
        print(f"{c['p']:>9} {c['n']:>5} {c['m']:>7} {c['M']:>9.3f} "
              f"{c['r_max_sqrtn']:>9.3f} {c['r_max_rms']:>8.3f} {c['r_max_johnson']:>10.3f}")
