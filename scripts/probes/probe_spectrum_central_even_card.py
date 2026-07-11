#!/usr/bin/env python3
"""
probe_spectrum_central_even_card.py  (#444, lane centraleven)

O230 (DeepBandSpectrumCentralNegInvariant) PROVED spectrum(n/2) = -spectrum(n/2) (negation-closed
at the self-complementary central depth, under sum_mu = 0). O230's module doc ASSERTS but does NOT
prove the consequence: "the central-depth spectrum cardinality is even -- its nonzero part splits
into +/- pairs unless a value is its own negative, which over a field of odd characteristic means
the value is 0".

This probe verifies that asserted-but-unproven consequence as a structural divisibility brick:
  (1) negation is a FIXED-POINT-FREE involution on F\{0} in odd char: -v = v => v = 0.
  (2) therefore |spectrum(n/2) \ {0}| is EVEN  (2 | |spectrum r \ {0}|),
      a NEW divisibility on the open obstruction |spectrum r| at the prize-critical central depth,
      independent of (and combinable with) O231's |mu| | |spectrum r \ {0}|.
  (3) cross-check: combined <mu,-1> orbit-divisibility lcm(2,|mu|) | |spectrum r \ {0}| at central r.
      (Since -1 in mu_n for n=2^a, this collapses to |mu| -- but the 2|... brick holds under the
       WEAKER hypothesis sum_mu=0 WITHOUT mu being a subgroup, so it is genuinely separate content.)

PROPER thin mu_n (n=2^a), p >> n^3, p == 1 mod n, multiple primes per n, NEVER n=q-1.
Plus a NON-subgroup negation-closed ground set (mu = {a,-a,b,-b,...}) to show 2|... does NOT need
the multiplicative-subgroup structure (only sum=0 + negation-closure of the ground set).
"""
import sys
from sympy import isprime, primitive_root
from itertools import combinations
import random

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

def main():
    total = fails = 0
    print("=== PART A: thin mu_n 2-power subgroups (prize regime) ===")
    for a in range(2, 5):           # n = 4,8,16
        n = 1 << a
        lo = n ** 3 + 1
        for p in find_primes(n, 3, lo):
            mu = muN(p, n)
            assert sum(mu) % p == 0, "mu_n must sum to 0 (n even)"
            r = n // 2
            spec = spectrum(mu, r, p)
            # (1) FPF: any nonzero v with -v=v?
            self_neg = [v for v in spec if v != 0 and (-v) % p == v]
            # (2) even card off zero
            nz = len(spec - {0})
            ok_fpf = (len(self_neg) == 0)
            ok_even = (nz % 2 == 0)
            total += 1
            if not (ok_fpf and ok_even):
                fails += 1
                print(f"  FAIL n={n} p={p}: self_neg={self_neg} nz={nz}")
            print(f"  n={n:2d} p={p:6d} r=n/2={r:2d}: |spec|={len(spec):5d} "
                  f"|spec_minus_0|={nz:5d} even={ok_even} fpf={ok_fpf} "
                  f"2|spec_minus_0={'Y' if nz%2==0 else 'N'} (|mu|={n}, |mu| divides? "
                  f"{'Y' if nz%n==0 else 'N'})")

    print("\n=== PART B: NON-subgroup negation-closed ground set (only sum=0 needed) ===")
    # Build mu = {x1,-x1,...,xk,-xk} (sum=0, negation-closed, NOT a mult subgroup).
    for p in [10007, 10009, 10037]:
        k = 4                      # |mu| = 2k = 8, central r = 4
        random.seed(p)
        xs = random.sample(range(1, p // 2), k)
        mu = sorted(set([x for x in xs] + [(-x) % p for x in xs]))
        if len(mu) != 2 * k:
            continue
        assert sum(mu) % p == 0
        # confirm NOT a multiplicative subgroup (1 likely not in mu / not closed)
        is_subgroup = (1 in mu) and all((a*b) % p in mu for a in mu for b in mu)
        r = k                      # central depth |mu|/2
        spec = spectrum(mu, r, p)
        # central negation-closure should hold (sum_mu=0); even card off zero
        neg = {(-v) % p for v in spec}
        nz = len(spec - {0})
        ok_negclosed = (neg == spec)
        ok_even = (nz % 2 == 0)
        total += 1
        if not (ok_negclosed and ok_even):
            fails += 1
            print(f"  FAIL p={p}: negclosed={ok_negclosed} even={ok_even}")
        print(f"  p={p} |mu|={len(mu)} subgroup={is_subgroup} r={r}: "
              f"|spec_minus_0|={nz} negclosed={ok_negclosed} even={ok_even}")

    print(f"\n=== {total} instances, {fails} fails ===")
    if fails == 0:
        print("VERIFIED: negation is FPF on F minus {0} (odd char) => 2 | |spectrum(n/2) \\ {0}|.")
        print("Part B shows the 2|... brick needs only sum_mu=0 + negation-closure, NOT subgroup.")
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
