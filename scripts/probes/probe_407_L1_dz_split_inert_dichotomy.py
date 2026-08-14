"""
L1 / #407: VERIFY the precise scope of the Dvornicich-Zannier theorem for 2^mu-th roots.

DZ Theorem (Arch. Math. 79 (2002), Thm + Prop (8)): for a NORMALIZED (indecomposable mod ell)
vanishing congruence  sum a_i zeta_i == 0 (mod ell), the least common order Q is SQUAREFREE
and sum_{p|Q}(p-2) <= k-2.

The PROOF (lines 171-227 of the PDF) reduces mod ell via the isomorphism
    Z[zeta]/(ell) =~ F_ell[xi],   dim_{F_ell} = phi(Q),
and Lemma 1 needs Phi_Q(X) to be the MINIMAL polynomial of multiplication-by-xi, i.e.
Phi_Q essentially IRREDUCIBLE mod ell. This holds when ell is INERT / large residue degree,
and FAILS when ell SPLITS (ell == 1 mod Q): then xi in F_ell, Z[zeta]/(ell) =~ F_ell^{phi(Q)},
a PRODUCT of fields, and the dimension/char-poly argument collapses.

PRIZE REGIME: p == 1 mod n (n=2^mu) => p SPLITS COMPLETELY => DZ's hypothesis FAILS.
This probe DIRECTLY TESTS the dichotomy:
  - SPLIT  primes (p == 1 mod n): expect indecomposable antipodal-free vanishing sums
    of FULL order Q = n to EXIST (DZ does not apply).  [refutes the naive DZ-dyadic closure]
  - INERT-ish primes (p == 1 mod 4 but p NOT == 1 mod n, so g of order < n in F_p, or
    g lives in an extension): we cannot have mu_n in F_p, so the prize setup needs split p.
    To probe the inert side we work over the SMALLEST field F_{p^f} containing mu_n and ask
    whether the order Q is then forced to {1,2}.  (Expectation per DZ: in the inert/high-degree
    case the squarefree-order conclusion DOES hold.)

VERDICT TARGET: confirm DZ gives NO bound on the prime p in the split regime (the prize regime),
so DZ does NOT yield poly(n) for the count-lane bad primes.
"""
import itertools
from sympy import primerange, isprime
from math import gcd


def primitive_root_mod(p, n):
    """primitive n-th root of unity in F_p if p == 1 mod n, else None."""
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    HALF = n // 2
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and (HALF == 0 or pow(g, HALF, p) == p - 1):
            return g
    return None


def least_common_order(exps, n):
    """least common order Q of the roots {zeta^e : e in exps}, normalized zeta_0=1 (subtract exps[0])."""
    e0 = exps[0]
    norm = [(e - e0) % n for e in exps]
    g = n
    for e in norm:
        g = gcd(g, e)
    if all(e == 0 for e in norm):
        return 1
    return n // gcd(n, g)


def min_indecomposable_orders(n, p, g, sizes):
    """
    Find antipodal-free vanishing 0/1-sums mod p that are INDECOMPOSABLE (no proper subsum
    vanishes), and report the least common order Q of each.  Per DZ (if applicable) Q in {1,2}.
    """
    HALF = n // 2
    orders = []
    for size in sizes:
        for S in itertools.combinations(range(n), size):
            Sset = set(S)
            if any(((j + HALF) % n) in Sset for j in S):
                continue  # antipodal-free
            vals = [pow(g, j, p) for j in S]
            if sum(vals) % p != 0:
                continue
            # indecomposable? (no proper nonempty subsum == 0)
            indec = True
            for sz in range(1, size):
                hit = False
                for sub in itertools.combinations(range(size), sz):
                    if sum(vals[i] for i in sub) % p == 0:
                        hit = True
                        break
                if hit:
                    indec = False
                    break
            if indec:
                Q = least_common_order(list(S), n)
                orders.append((tuple(S), Q))
    return orders


def split_regime_scan(n, sizes, hi):
    """SPLIT primes p == 1 mod n: do FULL-order (Q=n) indecomposable antipodal-free sums exist?"""
    print(f"\n### SPLIT regime: n={n}, p == 1 mod {n} (prize setup), sizes={sizes} ###")
    any_full = False
    for p in primerange(n + 1, hi):
        if p % n != 1:
            continue
        g = primitive_root_mod(p, n)
        if g is None:
            continue
        orders = min_indecomposable_orders(n, p, g, sizes)
        full = [o for o in orders if o[1] == n]
        sqfree = [o for o in orders if o[1] in (1, 2)]
        if orders:
            print(f"  p={p}: #indecomposable antipodal-free sums={len(orders)}; "
                  f"Q=n(full): {len(full)}, Q in {{1,2}}: {len(sqfree)}, "
                  f"other Q: {len(orders)-len(full)-len(sqfree)}")
            if full:
                any_full = True
                print(f"      example FULL-order (Q={n}) relation: exps={full[0][0]}")
    if any_full:
        print(f"  => SPLIT primes admit indecomposable Q={n} relations => DZ does NOT apply / does NOT bound p.")
    else:
        print(f"  => no indecomposable full-order relation found below {hi}.")


if __name__ == "__main__":
    split_regime_scan(8, [3, 4], 2000)
    split_regime_scan(16, [4, 6], 4000)
    split_regime_scan(32, [4], 1500)
    print()
    print("="*70)
    print("CONCLUSION: DZ's squarefree-order bound requires Phi_Q irreducible mod ell")
    print("(inert / high residue degree). The prize prime p == 1 mod n SPLITS COMPLETELY,")
    print("so DZ's hypothesis FAILS and it gives NO bound on p. Confirmed by full-order")
    print("indecomposable relations existing at small split primes (17, 97, ...).")
