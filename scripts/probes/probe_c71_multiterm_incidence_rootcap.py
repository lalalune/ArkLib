#!/usr/bin/env python3
"""
#444 -- C71 RESIDUAL LANE: the NON-orbit incidence bound on the 2- and 3-term strata.

Context (post-pivot, after C71DOM landed C71SparseOrbitGap.lean / 5dd3a409e):
  The June-16 ground-truth pivot relocated the prize to the above-Johnson O(1)/|F| regime,
  reduced by Chai-Fan 2026/861 to Conjecture 7.1 (worst-case FRI adversary is <=3-sparse).
  ActionOrbitGeneralF PINS that the O(1)/|F| action-orbit closure is MONOMIAL-only
  (eigenvector-gated). C71DOM's probe established ROUTE B: the worst-case <=3-sparse adversary is
  STRICTLY multi-term (s23max=9 > s1max=8), so it ESCAPES the orbit pin. The named-open residual =
  a NON-orbit incidence bound on the 2- and 3-term strata. NO worktree on it.

THE STRUCTURAL CLAIM TO PROBE (the formalizable non-orbit brick):
  A genuine m-term (m in {2,3}) direction f = sum_k c_k X^{e_k} (distinct exponents, char p > deg)
  has, at any nonzero point, root multiplicity < m (the in-tree SparseMultiplicity engine
  rootMultiplicity_sparse_lt). The DISTINCT-root count of an m-sparse f in mu_n is therefore
  bounded, and the per-line incidence governed by f's vanishing is controlled WITHOUT any orbit
  structure -- a pure polynomial-method (Descartes/confluent-Vandermonde) count.

  SHARP SUB-QUESTION (decisive, budget-feasible): for a genuine 2-term direction (binomial)
  f = X^i - c X^j over mu_n, is the number of mu_n-roots of f at most gcd(i-j, n) (the binomial
  root-count law: X^{i-j} = c has exactly gcd(i-j,n) or 0 solutions in mu_n)? And does this give a
  STRICTLY smaller per-direction incidence than the trivial deg-f bound, matching what the orbit
  count gives monomials -- so the multi-term strata are covered by a ROOT-COUNT bound, not an orbit
  count? This is the exact residual brick: binomial incidence = gcd-law, not orbit-law.

PROBE (EXACT, reproducible): thin mu_n = 2^a, p = 1 mod n, NEVER n = q-1, multi-prime incl p > n^3
and Fermat-type. For every genuine 2-term f = X^i - c X^j (c in mu_n, i != j):
  (1) ROOTCAP: #{x in mu_n : f(x)=0} <= gcd(|i-j|, n).
  (2) MULTIPLICITY: max root multiplicity of f at any nonzero point < 2 (m-sparse engine, m=2).
  (3) NON-orbit vs orbit baseline: the binomial root-count gcd(i-j,n) is achieved WITHOUT f being
      a dilation eigenvector (f is genuinely 2-term => not monomial => orbit-closure fails), yet
      the incidence is STILL clean -- i.e. the root-count covers what the orbit count cannot.
"""
import itertools
from math import gcd


def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True


def find_prime(n, want_gt_n3=False, start_mult=1):
    # smallest prime p = 1 mod n, optionally p > n^3
    k = start_mult
    # never allow n = p-1 (full group): require p-1 = k*n with k >= 2 (proper subgroup)
    target = n * n * n if want_gt_n3 else n + 1
    if k < 2:
        k = 2
    while True:
        p = k * n + 1
        if p > target and is_prime(p):
            return p
        k += 1


def mu_n(p, n):
    # the order-n subgroup of F_p^* : need n | p-1. Find a generator g, take g^((p-1)/n).
    assert (p - 1) % n == 0

    def order(a):
        o = 1
        x = a % p
        while x != 1:
            x = (x * a) % p
            o += 1
        return o

    g = 2
    while order(g) != p - 1:
        g += 1
    h = pow(g, (p - 1) // n, p)  # primitive n-th root of unity
    return [pow(h, t, p) for t in range(n)], h


def eval_poly_terms(terms, x, p):
    # terms = list of (coeff, exp)
    return sum((c * pow(x, e, p)) % p for c, e in terms) % p


def roots_in(elts, terms, p):
    return [x for x in elts if eval_poly_terms(terms, x, p) == 0]


def mult_at(terms, alpha, p, maxord=4):
    # numeric root multiplicity of poly at alpha (alpha != 0) by checking derivatives
    cur = list(terms)
    order = 0
    for _ in range(maxord + 1):
        v = sum((c * pow(alpha, e, p)) % p for c, e in cur) % p
        if v != 0:
            return order
        nxt = []
        for c, e in cur:
            if e > 0:
                nxt.append(((c * e) % p, e - 1))
        cur = [(c, e) for c, e in nxt if c % p != 0]
        order += 1
        if not cur:
            return order
    return order


def run():
    cases = []
    for a in (2, 3, 4):
        n = 1 << a
        for want_gt in (False, True):
            p = find_prime(n, want_gt_n3=want_gt)
            cases.append((n, p))
    for (n, p) in [(8, 257), (16, 257)]:
        if (p - 1) % n == 0 and is_prime(p):
            cases.append((n, p))

    print(f"{'n':>3} {'p':>6} {'>n^3':>5} | "
          f"{'rootcap_ok':>10} {'mult<2_ok':>9} {'tested':>7} {'gcd_tight':>9}")
    all_rootcap = True
    all_mult = True
    for (n, p) in cases:
        assert n != p - 1, "n must be PROPER subgroup, never q-1"
        elts, h = mu_n(p, n)
        rootcap_ok = True
        mult_ok = True
        tested = 0
        gcd_tight_hits = 0
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                d = gcd(abs(i - j), n)
                for c in elts:
                    terms = [(1, i), ((-c) % p, j)]
                    rs = roots_in(elts, terms, p)
                    tested += 1
                    if len(rs) > d:
                        rootcap_ok = False
                    if len(rs) == d and d > 0:
                        gcd_tight_hits += 1
                    for r in rs:
                        if mult_at(terms, r, p) >= 2:
                            mult_ok = False
        all_rootcap = all_rootcap and rootcap_ok
        all_mult = all_mult and mult_ok
        print(f"{n:>3} {p:>6} {str(p>n**3):>5} | "
              f"{str(rootcap_ok):>10} {str(mult_ok):>9} {tested:>7} {gcd_tight_hits:>9}")

    print()
    print(f"VERDICT rootcap (#roots(binomial in mu_n) <= gcd(|i-j|,n)) ALL: {all_rootcap}")
    print(f"VERDICT mult<2 (2-sparse engine, no double roots at nonzero pts) ALL: {all_mult}")
    print()
    print("INTERPRETATION: if both TRUE, the genuine 2-term (multi-term) strata's mu_n-incidence is")
    print("governed by the BINOMIAL gcd-root-count + the m-sparse mult<m engine -- a NON-ORBIT")
    print("polynomial-method bound (Descartes/confluent-Vandermonde), covering exactly the worst-")
    print("case strata (route B) the action-orbit O(1)/|F| pin provably MISSES. The formalizable")
    print("residual brick: binomial-direction mu_n root-count <= gcd-law, mult<2, axiom-clean,")
    print("EXTENDING the in-tree SparseMultiplicity.rootMultiplicity_sparse_lt engine.")


if __name__ == "__main__":
    run()
