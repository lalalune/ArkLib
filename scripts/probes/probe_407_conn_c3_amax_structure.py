#!/usr/bin/env python3
"""
#407 C3 (part 2) — the STRUCTURE of a_max (max multiplicity), the energy-upper-bound driver.

From part 1:
  - r=2: a_max = n EXACTLY, q-INDEPENDENT (all primes, all n).
  - r>=2: in the SATURATED regime (small p) a_max inflates; in the NON-SATURATED (large p =
    PRIZE) regime a_max SETTLES to a fixed q-independent value.

CLAIM TO TEST: in the non-saturated/prize regime, a_max is q-INDEPENDENT and equals the CHAR-0
max multiplicity (= the max number of ordered r-tuples of mu_n summing to a fixed value IN Z[zeta_n]).
If so, then  E_r <= a_max * n^r  is a q-INDEPENDENT (count/char-0-controlled) UPPER bound on energy.

We compute:
  (1) a_max over a long prime sweep to find the settled (large-p) value a_max^inf.
  (2) the CHAR-0 max multiplicity a_max^0: enumerate r-tuples, map to the Z[zeta_n] coord vector
      (basis 1,z,...,z^{n/2-1}, z^{n/2}=-1), count multiplicities of exact ring elements.
  (3) compare a_max^inf vs a_max^0 vs N_r vs the diagonal floor n^{r-1}.
  (4) the resulting energy upper bound  E_r <= a_max^0 * n^r  vs the actual large-p E_r and the
      char-0 energy (2r-1)!! n^r (dyadic Wick).
"""
import sys, itertools
from collections import Counter
from sympy import isprime, primitive_root

def first_prime_1modn(n, lo):
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while not isprime(p):
        p += n
    return p

def primitive_nth_root(n, p):
    g = primitive_root(p)
    return pow(g, (p - 1)//n, p)

def char0_coord(exps, n):
    """Coordinate vector in Z[zeta_n] basis {1,z,...,z^{n/2-1}} (z^{n/2}=-1) of sum of z^{e}."""
    half = n//2
    v = [0]*half
    for e in exps:
        e %= n
        if e < half:
            v[e] += 1
        else:
            v[e-half] -= 1
    return tuple(v)

def fp_a(n, p, r):
    w = primitive_nth_root(n, p)
    roots = [pow(w, j, p) for j in range(n)]
    a = Counter()
    for tup in itertools.product(range(n), repeat=r):
        s = 0
        for j in tup: s = (s + roots[j]) % p
        a[s] += 1
    return a

def char0_a(n, r):
    a = Counter()
    for tup in itertools.product(range(n), repeat=r):
        a[char0_coord(tup, n)] += 1
    return a

def double_factorial(k):
    # (2r-1)!!
    res = 1
    while k > 0:
        res *= k; k -= 2
    return res

def main():
    print("="*100)
    print("C3 part 2: is a_max (energy-upper-bound driver) q-INDEPENDENT = char-0 max multiplicity?")
    print("="*100)

    for (mu, r) in [(3,2),(3,3),(4,2),(4,3),(5,2),(5,3)]:
        n = 2**mu
        if n**r > 5_000_000:
            continue
        # char-0 reference
        a0 = char0_a(n, r)
        a0_max = max(a0.values())
        N0 = len(a0)                       # char-0 sumset size (distinct ring elements)
        E0 = sum(v*v for v in a0.values()) # char-0 energy
        wick = double_factorial(2*r-1) * n**r
        # prime sweep, large primes (non-saturated/prize-like)
        primes = []
        for tgt in [n**3, n**4, n**5, n**6]:
            primes.append(first_prime_1modn(n, tgt))
        print(f"\n### n={n}, r={r}: char-0  a_max^0={a0_max}, N_r^0={N0}, E_r^0={E0}, Wick (2r-1)!!n^r={wick}")
        print(f"    diag floor n^(r-1)={n**(r-1)}, n^r={n**r}")
        print(f"{'p':>12} {'N_r':>7} {'a_max':>7} {'E_r':>11} {'a_max==a0?':>11} "
              f"{'E_r==E0?':>9} {'ub=a0*n^r':>11} {'E_r<=ub':>8}")
        for p in primes:
            a = fp_a(n, p, r)
            am = max(a.values()); Nr = len(a); Er = sum(v*v for v in a.values())
            ub = a0_max * n**r
            print(f"{p:>12} {Nr:>7} {am:>7} {Er:>11} {str(am==a0_max):>11} "
                  f"{str(Er==E0):>9} {ub:>11} {'OK' if Er<=ub else 'FAIL':>8}")

    print("\n" + "="*100)
    print("CONCLUSION CHECK:")
    print(" - Is a_max q-independent (= char-0 a_max) in non-saturated regime? (look at a_max==a0 column)")
    print(" - If YES: E_r <= a_max^0 * n^r is a CHAR-0 (q-independent) upper bound on energy.")
    print(" - Is that bound NON-TRIVIAL vs Wick? Compare ub=a0*n^r to Wick=(2r-1)!!n^r.")

if __name__ == "__main__":
    main()
