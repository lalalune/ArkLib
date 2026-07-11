#!/usr/bin/env python3
"""
probe_spectrum_dilation_divisibility.py  (#444, lane spectrumdvd)

DeepBandSpectrumComplementSymmetry pins the PALINDROME |spectrum r| = |spectrum (n-r)| on the
open prize obstruction |spectrum r| = |{ sum_{z in S} z : S in powersetCard r mu }| (BCHKS 1.12),
but computes NO further structure. This probe tests a NEW structural constraint the palindrome
file lacks:

  for a MULTIPLICATIVE SUBGROUP mu = mu_n (closed under *), the subset-sum spectrum is CLOSED
  under multiplication by every g in mu_n:  g * spectrum(mu,r) = spectrum(mu,r).
  Proof mechanism: g*mu = mu (group), so S |-> g*S is a bijection on powersetCard r mu, and
  sum_{z in g*S} z = g * sum_{z in S} z. Hence the spectrum is a union of mu_n-ORBITS under the
  scaling action, so:
     |spectrum r \ {0}|  is DIVISIBLE BY  the common orbit size,
  and in the free case (every nonzero spectrum value has full stabilizer trivial) by n itself.

We measure, on PROPER thin mu_n (n=2^a), prize-regime p >> n^3, p == 1 mod n, NEVER n=q-1:
  (A) g * spectrum == spectrum for every g in mu_n  (set-level invariance).
  (B) the multiset of mu_n-orbit sizes on spectrum \ {0}: report whether ALL are = n (free => n | card),
      or some are proper divisors of n (a nonzero spectrum value fixed by a nontrivial subgroup).
  (C) so the HONEST divisible-by claim: spectrum\{0} card is a sum of orbit sizes (each | n);
      report gcd of orbit sizes and whether n | |spectrum\{0}|.
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

def orbit_sizes(spec_nz, mu, p):
    """mu_n acts by scaling; partition spec_nz into orbits, return list of sizes."""
    spec = set(spec_nz)
    sizes = []
    seen = set()
    for v in spec_nz:
        if v in seen:
            continue
        orb = {(g * v) % p for g in mu}
        # orbit must stay inside spectrum if invariance holds
        sizes.append(len(orb))
        seen |= orb
    return sizes

def main():
    total = inv_fails = 0
    n_divides_all = True
    for a in range(2, 6):           # n = 4,8,16,32
        n = 1 << a
        lo = n ** 3 + 1
        # depth range: avoid the intractable central binomials C(32,16)~6e8.
        # invariance is depth-uniform; small r + (by complement) near-full r exercise it.
        depths = sorted(set(list(range(1, min(n, 6))) + [n - 1, n - 2, n - 3]))
        depths = [r for r in depths if 1 <= r < n]
        for p in find_primes(n, 3, lo):
            mu = muN(p, n)
            assert len(mu) == n and 1 in mu
            for r in depths:
                spec = spectrum(mu, r, p)
                # (A) set-level invariance g*spectrum == spectrum
                ok_inv = all({(g * v) % p for v in spec} == spec for g in mu)
                total += 1
                if not ok_inv:
                    inv_fails += 1
                    print(f"FAIL invariance n={n} p={p} r={r}")
                    continue
                spec_nz = [v for v in spec if v != 0]
                sizes = orbit_sizes(spec_nz, mu, p)
                # every orbit size divides n
                bad = [s for s in sizes if n % s != 0]
                if bad:
                    print(f"FAIL orbit-size-not-dividing-n n={n} p={p} r={r} sizes={sizes}")
                    inv_fails += 1
                    continue
                g_orb = reduce(gcd, sizes, n) if sizes else n
                card_nz = len(spec_nz)
                if card_nz % n != 0:
                    n_divides_all = False
                # report only the structural facts for a couple of depths
                if r in (1, 2, n // 2, n - 1):
                    free = all(s == n for s in sizes)
                    print(f"n={n:2d} p={p:6d} r={r:2d}: |spec|={len(spec):3d} "
                          f"|spec\\0|={card_nz:3d} orbits={len(sizes):2d} "
                          f"all-free={free} gcd_orbit={g_orb} n|card_nz={card_nz % n == 0}")
    print(f"\n=== {total} (n,p,r) instances, {inv_fails} invariance/orbit fails ===")
    print(f"n | |spectrum\\0| for ALL instances: {n_divides_all}")
    if inv_fails == 0:
        print("VERIFIED: spectrum is mu_n-scaling-invariant; spectrum\\0 is a union of mu_n-orbits,")
        print("each orbit size divides n. (Honest claim: invariance + orbit-size | n; full n|card")
        print("only in the free case.)")
    sys.exit(1 if inv_fails else 0)

if __name__ == "__main__":
    main()
