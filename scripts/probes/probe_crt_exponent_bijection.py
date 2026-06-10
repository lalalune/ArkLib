#!/usr/bin/env python3
"""Issue #232 — falsify-first probe for the CRT exponent bijection (de Bruijn step 2).

Claim under test (the normalization that will be formalized):
  n = N*M, gcd(N,M) = 1, zeta a primitive n-th root, xi = zeta^M, eta = zeta^N.
  FORWARD map g(j,c) = (j*M + c*N) mod n  for (j,c) in [0,N) x [0,M):
    (F1) g is a bijection onto Z/n            [no Bezout needed in this direction]
    (F2) zeta^(g(j,c)) = xi^j * eta^c          [trivial exponent arithmetic — checked]
  INVERSE map (Bezout normalization, recorded for the docstring):
    with u = M^{-1} mod N, v = N^{-1} mod M:
    (B1) e |-> (u*e mod N, v*e mod M) inverts g
    (B2) zeta^e = xi^(u*e mod N) * eta^(v*e mod M)
  SUM identity (the deliverable's statement, exact in Z[X]/(X^n - 1)):
    (S) for any S subset Z/n, with I = { (j,c) in grid : g(j,c) in S }:
        sum_{e in S} zeta^e  =  sum_{(j,c) in I} xi^j * eta^c
    — equivalent to the multiset of exponents {g(j,c) : (j,c) in I} equaling S,
      so it is checked EXACTLY (integer multisets), no floating point needed.
  Numeric double-check of (F2)/(B2) in complex floats as a second witness.

Exit 0 iff all checks pass; any violation prints and exits 1.
"""

import cmath
import itertools
import math
import random
import sys

random.seed(232)

FAIL = 0
CHECKS = 0


def check(cond, msg):
    global FAIL, CHECKS
    CHECKS += 1
    if not cond:
        FAIL += 1
        print(f"VIOLATION: {msg}")


def probe_point(N, M):
    n = N * M
    assert math.gcd(N, M) == 1
    grid = list(itertools.product(range(N), range(M)))

    # (F1) forward bijection
    g = {(j, c): (j * M + c * N) % n for (j, c) in grid}
    image = sorted(g.values())
    check(image == list(range(n)), f"(F1) g not bijective at N={N},M={M}: {image}")

    # Bezout normalization
    u = pow(M, -1, N)
    v = pow(N, -1, M)
    for e in range(n):
        j, c = (u * e) % N, (v * e) % M
        check(g[(j, c)] == e, f"(B1) inverse fails at e={e}, N={N}, M={M}")

    # (F2)/(B2) numeric: zeta^e == xi^j * eta^c
    zeta = cmath.exp(2j * cmath.pi / n)
    xi, eta = zeta**M, zeta**N
    for e in range(n):
        j, c = (u * e) % N, (v * e) % M
        lhs = zeta**e
        rhs = (xi**j) * (eta**c)
        check(abs(lhs - rhs) < 1e-9,
              f"(B2) zeta^e != xi^j*eta^c at e={e} (j={j},c={c}), N={N},M={M}, "
              f"|diff|={abs(lhs-rhs):.2e}")

    # (S) sum identity, exact multiset form, all subsets if n small else sampled
    subsets = []
    if n <= 16:
        subsets = [frozenset(s) for r in range(n + 1)
                   for s in itertools.combinations(range(n), r)]
    else:
        subsets = [frozenset(random.sample(range(n), random.randint(0, n)))
                   for _ in range(2000)]
    for S in subsets:
        I = [(j, c) for (j, c) in grid if g[(j, c)] in S]
        ms = sorted(g[x] for x in I)
        check(ms == sorted(S), f"(S) multiset mismatch at N={N},M={M}, S={sorted(S)}")
    return len(subsets)


def main():
    total_subsets = 0
    points = [(4, 3), (3, 4), (3, 5), (5, 3), (8, 9), (9, 8), (4, 9), (25, 4)]
    for (N, M) in points:
        total_subsets += probe_point(N, M)
        print(f"point N={N}, M={M} (n={N*M}): OK")

    # control: drop coprimality — bijection MUST fail (apophenia guard)
    N, M = 4, 6
    n = N * M
    g_vals = sorted(((j * M + c * N) % n)
                    for j in range(N) for c in range(M))
    check(g_vals != list(range(n)),
          "(control) non-coprime grid map unexpectedly bijective at N=4,M=6")
    print(f"control N=4, M=6 non-coprime: bijection fails as expected "
          f"(image card {len(set(g_vals))} < {n})")

    print(f"\nchecks: {CHECKS}, violations: {FAIL}, subset-sum identities: {total_subsets}")
    if FAIL:
        sys.exit(1)
    print("ALL OK — normalization fixed: g(j,c) = j*M + c*N mod n; "
          "inverse (u*e mod N, v*e mod M) with u=M^{-1} mod N, v=N^{-1} mod M; "
          "zeta^e = xi^(u*e) * eta^(v*e).")


if __name__ == "__main__":
    main()
