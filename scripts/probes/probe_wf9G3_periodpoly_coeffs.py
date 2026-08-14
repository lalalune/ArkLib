#!/usr/bin/env python3
"""
#444 LANE G3 — period-polynomial COEFFICIENT route to bounding M(n).

The Gaussian periods eta_0..eta_{m-1} of the dyadic subgroup mu_n (order n=2^mu, n|p-1,
m=(p-1)/n) are the roots of the degree-m period polynomial
        Psi(T) = prod_i (T - eta_i)  in  Z[T],
whose coefficients (up to sign) are the elementary symmetric functions e_k(eta) -- the
classical cyclotomic numbers.  M(n) = max_i |eta_i|.

QUESTION (G3 mission): does the 2-power structure force the coefficients to be small enough
that a classical ROOT BOUND (Cauchy / Fujiwara / Lagrange) gives  M(n) <= C sqrt(n log(p/n)) ?

Classical root bounds for monic Psi(T)=T^m + c_{m-1}T^{m-1}+...+c_0 (c_k = (-1)^{m-k} e_{m-k}):
  Cauchy:   max|root| <= 1 + max_k |c_k|
  Fujiwara: max|root| <= 2 * max_k |c_k / 1|^{1/(m-k)}  = 2 max_k |e_{m-k}|^{1/(m-k)}  ... careful
  Lagrange: max|root| <= max(1, sum_k |c_k|)
The SHARP statement we actually need: M(n) = sup-norm of the period vector. A coefficient bound
gives an UPPER bound on M(n); we ask whether (a) the coefficients are computable exactly for
dyadic n, and (b) the resulting root bound matches sqrt(n log(p/n)) or is wildly loose.

We compute coefficients EXACTLY: the periods are algebraic integers; the power sums
   p_k = sum_i eta_i^k = (number of solutions structure) are INTEGERS, computed by counting.
Then Newton's identities give the integer e_k exactly (no float).  p_1 = sum eta_i = -1
(since sum over all nonzero residues of zeta = -1).  p_k = sum over m cosets of (coset sum)^k,
which equals (1/?) ... we compute p_k = sum_{i} eta_i^k directly by EXACT cyclotomic arithmetic
in Z[zeta_p] reduced via the period idempotents -- but the cleanest exact route is:

   p_k = sum_{b in F_p^*} (eta over coset of b)^k / n   NO.

EXACT power sums via the trace: eta_i^k expands as a sum of zeta_p^{(sum of k coset elements)};
p_k = sum_i eta_i^k = sum over (k-tuples from a common coset, summed over cosets) zeta_p^{s}.
Grouping by the value s mod p and using sum_{i} [exponent in coset i]:  the TOTAL coefficient of
zeta_p^t in sum_i eta_i^k is N_k(t) = #{(x_1..x_k) all in a common coset C : x_1+...+x_k = t}.
Then p_k = sum_t N_k(t) zeta^t.  Since p_k is a rational integer, p_k = N_k(0) - (1/(p-1)) sum_{t!=0}...
Actually: sum_t N_k(t) zeta^t with zeta a primitive p-th root: rational => equals
   p_k = N_k(0) - A   where A = common value of N_k(t) for t != 0 (it is constant in t!=0 by
   Galois on the FULL group only if k-tuples come from a single coset... it's NOT constant in
   general).  So we compute p_k exactly by EXACT algebraic-number arithmetic over Q(zeta_p).

We use sympy's exact cyclotomic arithmetic (minpoly reduction) for SMALL p, and report:
  - exact integer coefficients e_k (cyclotomic numbers),
  - max_k |e_k|^{1/k}  and the Fujiwara/Cauchy root bounds,
  - actual M(n) (max|eta_i|, high-precision),
  - ratio of each bound to the conjectured sqrt(n log(p/n)).
"""
import math
from math import gcd, log, sqrt
import sympy
from sympy import Poly, symbols, Rational, nsimplify

def primitive_root(p):
    fac = sympy.factorint(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def cosets(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    sub = [pow(g, (m * j) % (p - 1), p) for j in range(n)]   # mu_n
    cos = []
    for i in range(m):
        rep = pow(g, i, p)
        cos.append([(rep * s) % p for s in sub])
    return m, cos

def power_sums_exact(p, n, kmax):
    """p_k = sum_i eta_i^k as EXACT integers, by counting k-tuples within a coset by sum mod p.
       sum_i eta_i^k = sum_t N_k(t) zeta^t, N_k(t)=#{k-tuples in one coset with sum=t, summed over cosets}.
       Because the result is a rational integer and {zeta^t: t=1..p-1} has the single relation
       1+zeta+...+zeta^{p-1}=0, we have  p_k = N_k(0) - N_k(1)  IS WRONG in general; instead
       sum_t N_k(t) zeta^t = N_k(0)*1 + sum_{t=1}^{p-1} N_k(t) zeta^t.  Writing it in the integral
       basis 1,zeta,...,zeta^{p-2} with zeta^{p-1} = -(1+...+zeta^{p-2}):
         = (N_k(0)-N_k(p-1)) + sum_{t=1}^{p-2}(N_k(t)-N_k(p-1)) zeta^t.
       This is a rational integer IFF N_k(t) is CONSTANT for t=1..p-1; then p_k = N_k(0)-N_k(1).
       It is NOT generally constant, so p_k is genuinely a cyclotomic-period integer combination
       that still lands in Z (since p_k=trace-like).  We therefore compute it EXACTLY by:
         p_k = N_k(0) - (1/(p-1)) * sum_{t=1}^{p-1} N_k(t)
       PROOF: sum_t N_k(t) = total #k-tuples = m*n^k.  The non-trivial part sum_{t!=0}N_k(t)zeta^t
       has rational part -(1/(p-1)) sum_{t!=0} N_k(t) (avg of zeta^t over t!=0 is -1/(p-1)) ONLY
       when the multiset {N_k(t)}_{t!=0} is Galois-stable, which it IS: t -> c*t (c in mu_n... no, c
       in F_p^*) permutes cosets-sums? multiplying every coordinate by c in F_p^* maps a coset to a
       coset and scales the sum by c, so N_k(t)=N_k(ct) for all c in F_p^* => N_k constant on F_p^*!
       Hence p_k = N_k(0) - N_k(1) EXACTLY.  (rigorous)
    """
    m, cos = cosets(p, n)
    res = []
    for k in range(1, kmax + 1):
        # N_k(t) for t in {0,1}: count k-tuples within a single coset summing to t mod p, over all cosets.
        # Direct enumeration is n^k * m -- only feasible for tiny n,k.  Use convolution of per-coset
        # multiplicity vectors instead: for each coset C, build indicator over Z/p, self-convolve k times.
        import numpy as np
        N0 = 0; N1 = 0
        for C in cos:
            vec = np.zeros(p, dtype=object)
            for x in C:
                vec[x] += 1
            acc = vec.copy()
            for _ in range(k - 1):
                # circular convolution mod p (exact integer)
                new = np.zeros(p, dtype=object)
                nz = np.nonzero(acc)[0]
                nz2 = np.nonzero(vec)[0]
                for a in nz:
                    av = acc[a]
                    for b in nz2:
                        new[(a + b) % p] += av * vec[b]
                acc = new
            N0 += int(acc[0]); N1 += int(acc[1])
        res.append(N0 - N1)   # p_k exactly
    return m, res

def elem_from_power(p_sums, m):
    """Newton's identities: e_0=1, e_k = (1/k) sum_{i=1}^k (-1)^{i-1} e_{k-i} p_i, k=1..m."""
    e = [Rational(1)]
    for k in range(1, m + 1):
        s = Rational(0)
        for i in range(1, k + 1):
            s += (-1) ** (i - 1) * e[k - i] * p_sums[i - 1]
        e.append(s / k)
    return e  # e[0..m]; all should be integers

def analyze(p, n, kmax=None):
    m, cos = cosets(p, n)
    K = m if kmax is None else min(kmax, m)
    _, psums = power_sums_exact(p, n, K)
    # exact periods (high precision) for M(n) and verification
    import mpmath as mp
    mp.mp.dps = 50
    zeta = mp.e ** (2j * mp.pi / p)
    eta = [mp.fsum(zeta ** z for z in C) for C in cos]
    Mn = float(max(abs(e) for e in eta))
    # verify power sums against float
    psum_float = [float(mp.re(mp.fsum(e ** k for e in eta))) for k in range(1, K + 1)]
    perr = max(abs(psums[i] - psum_float[i]) for i in range(K))
    out = {'p': p, 'n': n, 'm': m, 'psums': psums, 'psum_err': perr, 'Mn': Mn}
    if kmax is None:
        e = elem_from_power(psums, m)
        # all e_k integers?
        ints = [sympy.nsimplify(x) for x in e]
        e_int = [int(x) if x == int(x) else None for x in e]
        out['e'] = e_int
        # Cauchy bound: 1 + max_k |e_k| (coeff c_{m-k}=(-1)^k e_k)
        coeffs = [abs(e[k]) for k in range(1, m + 1)]
        cauchy = 1 + max(float(c) for c in coeffs)
        # Fujiwara: 2 * max_k |e_k|^{1/k}
        fuj = 2 * max((float(abs(e[k]))) ** (1.0 / k) if e[k] != 0 else 0 for k in range(1, m + 1))
        out['cauchy'] = cauchy
        out['fujiwara'] = fuj
    return out

if __name__ == "__main__":
    print("=" * 110)
    print("G3: period-polynomial COEFFICIENT (cyclotomic-number) route to M(n) bound.")
    print("EXACT integer power sums p_k = N_k(0)-N_k(1) (Galois-constant argument), Newton -> e_k.")
    print("=" * 110)
    den = lambda n, m: sqrt(n * log(m)) if m > 1 else 1.0
    # dyadic n, small m so exact e_k tractable
    CASES = [
        (4, [13, 29, 53, 61, 109, 157]),
        (8, [41, 73, 89, 97, 113]),
        (16, [97, 113, 193, 241, 337]),
        (32, [97, 193, 257, 353, 449]),
        (64, [193, 257, 449, 577]),
    ]
    print(f"{'p':>6} {'n':>4} {'m':>4} | {'M(n)':>7} {'sqrt(n ln m)':>12} {'M/√':>6} | "
          f"{'Cauchy':>9} {'Fujiwara':>9} {'Fuj/M':>7} {'e_k int?':>8} {'p_k err':>9}")
    print("-" * 110)
    for n, primes in CASES:
        for p in primes:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 2 or m > 9:
                continue
            try:
                r = analyze(p, n)
            except Exception as ex:
                print(f"{p:>6} {n:>4} {m:>4} | ERROR {ex}")
                continue
            d = den(n, m)
            allint = all(x is not None for x in r['e'])
            print(f"{p:>6} {n:>4} {m:>4} | {r['Mn']:>7.3f} {d:>12.3f} {r['Mn']/d:>6.3f} | "
                  f"{r['cauchy']:>9.2e} {r['fujiwara']:>9.3f} {r['fujiwara']/r['Mn']:>7.3f} "
                  f"{str(allint):>8} {r['psum_err']:>9.1e}")
    print("-" * 110)
