#!/usr/bin/env python3
"""
probe_spectrum_freeness_discharge.py  (#444, lane specfree)

O229 (DeepBandSpectrumDilationInvariant) proved the subset-sum spectrum is mu_n-dilation
invariant (spectrum_smul_invariant) and a generic uniform-orbit divisibility lemma
(card_dvd_of_uniform_orbit_partition) that is GATED ON A FREENESS HYPOTHESIS (every nonzero
spectrum value has a fibre of size exactly |mu|). O229's report records freeness as an
EMPIRICAL observation, left as a hypothesis, "not baked in".

This probe confirms the freeness is NOT empirical but a FIELD-ARITHMETIC THEOREM that can be
discharged unconditionally:

  the dilation action of a finite multiplicative subgroup mu on F \ {0} is FREE:
      for v != 0 and g in mu,  g * v = v  =>  g = 1
  (because (g - 1) * v = 0 in a field with v != 0 forces g = 1).

So the stabiliser of every NONZERO spectrum value is trivial, every nonzero-spectrum orbit has
size exactly |mu|, and therefore  |mu|  |  |spectrum r \ {0}|  UNCONDITIONALLY (the exact lemma
this discharges is `dilation_free` already in I031DilationOrbitReduction.lean -- reused here, no
new field fact invented).

We verify on PROPER thin mu_n (n = 2^a), prize-regime p >> n^3, p == 1 mod n, multiple primes,
NEVER n = q - 1:
  (A) g*v = v with v in spectrum\{0}, g in mu  =>  g = 1  (pointwise freeness, the mechanism).
  (B) hence EVERY nonzero-spectrum mu-orbit has size exactly n, and n | |spectrum r \ {0}|
      with NO freeness assumption (it is forced).
"""
import sys
from sympy import isprime, primitive_root
from itertools import combinations
from math import gcd
from functools import reduce


def find_primes(n, count, lo):
    out, p = [], lo - (lo % n) + 1
    while len(out) < count:
        if p > n and isprime(p) and (p - 1) % n == 0:
            out.append(p)
        p += n
    return out


def muN(p, n):
    g = primitive_root(p)
    e = (p - 1) // n
    base = pow(g, e, p)
    return sorted({pow(base, j, p) for j in range(n)})


def spectrum(mu, r, p):
    return {sum(S) % p for S in combinations(mu, r)}


def run():
    free_fail = 0          # (A) pointwise freeness violations
    orbit_nonfull = 0      # (B) any nonzero-spectrum orbit of size < n
    dvd_fail = 0           # (B) n does not divide |spectrum\{0}|
    total = 0
    examples = []
    for a in range(3, 6):          # n = 8, 16, 32
        n = 1 << a
        lo = n ** 3 + 1            # prize-regime p >> n^3
        primes = find_primes(n, 3, lo)
        for p in primes:
            mu = muN(p, n)
            assert len(mu) == n and 0 not in mu
            # depths: small r and (by complement) near-full; cap on binomial blowup
            depths = [r for r in (1, 2, 3, n - 2, n - 1) if 0 <= r <= n]
            if n <= 16:
                depths = sorted(set(depths) | {4, 5})
            for r in depths:
                if r < 0 or r > n:
                    continue
                # avoid intractable central binomials
                from math import comb
                if comb(n, r) > 2_000_000:
                    continue
                spec = spectrum(mu, r, p)
                spec_nz = sorted(v for v in spec if v != 0)
                total += 1
                # (A) pointwise freeness: g*v == v (g in mu) => g == 1
                for v in spec_nz:
                    for g in mu:
                        if (g * v) % p == v % p and g != 1:
                            free_fail += 1
                # (B) orbit partition under mu-scaling
                seen = set()
                orbit_sizes = []
                for v in spec_nz:
                    if v in seen:
                        continue
                    orb = {(g * v) % p for g in mu}
                    orbit_sizes.append(len(orb))
                    seen |= orb
                if any(s != n for s in orbit_sizes):
                    orbit_nonfull += 1
                if len(spec_nz) % n != 0:
                    dvd_fail += 1
                if len(examples) < 8:
                    examples.append((n, p, r, len(spec_nz), len(spec_nz) // n if spec_nz else 0))
    print("instances:", total)
    print("(A) pointwise-freeness violations (g*v=v, g!=1):", free_fail)
    print("(B) nonzero-spectrum orbits of size < n         :", orbit_nonfull)
    print("(B) n does NOT divide |spectrum\\{0}|            :", dvd_fail)
    print("examples (n, p, r, |spec\\0|, |spec\\0|/n):")
    for e in examples:
        print("   ", e)
    ok = (free_fail == 0 and orbit_nonfull == 0 and dvd_fail == 0)
    print("VERDICT:", "FREENESS DISCHARGED unconditionally; n | |spectrum\\{0}|" if ok
          else "COUNTEREXAMPLE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(run())
