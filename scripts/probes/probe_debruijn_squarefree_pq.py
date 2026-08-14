#!/usr/bin/env python3
"""Probe (#232, de Bruijn step 3 base case): complete classification at squarefree n = pq.

CLAIM (to be formalized in DeBruijnSquarefreePQ.lean): for distinct primes p, q,
n = pq, zeta a primitive n-th root of unity (char 0), and S a subset of Z_n
(exponent set), the following are equivalent:
  (1) sum_{e in S} zeta^e = 0
  (2) on the CRT grid I = {(j,c) in [0,p) x [0,q) : (j*q + c*p) mod n in S},
      I = A x [0,q) for some A, or I = [0,p) x T for some T.
Equivalently: S is a disjoint union of rotated q-packets (cosets of p*Z_n),
or a disjoint union of rotated p-packets (cosets of q*Z_n) -- PURE unions only.

Exact char-0 arithmetic: the indicator polynomial of S reduced mod Phi_n(x) over ZZ.
Exhaustive over all 2^n subsets for n = 6, 15; sampled + structured for n = 35.
Also checks the RIGIDITY dichotomy used in the proof: subsets of mu_p with equal
sums are equal or {empty, full} -- exhaustively at p = 3, 5, 7, 11, 13.

Exit 0 iff all checks pass.
"""
import itertools, random, sys
from sympy import Poly, symbols, cyclotomic_poly, ZZ

x = symbols("x")

def vanishes(S, n, phi):
    """Exact: does sum_{e in S} zeta^e = 0 for zeta primitive n-th root?"""
    if not S:
        return True
    coeffs = [0] * n
    for e in S:
        coeffs[e % n] += 1
    p = Poly(list(reversed(coeffs)), x, domain=ZZ)
    return p.rem(phi).is_zero

def is_pure(S, p, q):
    """Grid purity: I = A x full or full x T."""
    n = p * q
    I = {(j, c) for j in range(p) for c in range(q) if (j * q + c * p) % n in S}
    Sset = set(e % n for e in S)
    assert len(I) == len(Sset), "CRT bijection size mismatch"
    cols = {j for (j, c) in I}
    rows = {c for (j, c) in I}
    colform = I == {(j, c) for j in cols for c in range(q)}
    rowform = I == {(j, c) for j in range(p) for c in rows}
    return colform or rowform

def check_pq(p, q, exhaustive, samples=200000):
    n = p * q
    phi = Poly(cyclotomic_poly(n, x), x, domain=ZZ)
    bad = 0
    nvan = 0
    if exhaustive:
        universe = list(range(n))
        for mask in range(2 ** n):
            S = [e for e in universe if (mask >> e) & 1]
            v = vanishes(S, n, phi)
            pure = is_pure(S, p, q)
            if v != pure:
                bad += 1
                if bad < 5:
                    print(f"  MISMATCH n={n} S={S} vanishes={v} pure={pure}")
            if v:
                nvan += 1
        print(f"  n={n}={p}*{q}: exhaustive 2^{n}, vanishing={nvan}, mismatches={bad}")
    else:
        rng = random.Random(232)
        # (a) all pure forms vanish (exhaustive over forms is 2^p + 2^q, do it)
        for A in itertools.chain.from_iterable(
                itertools.combinations(range(p), r) for r in range(p + 1)):
            S = [(j * q + c * p) % n for j in A for c in range(q)]
            if not vanishes(S, n, phi):
                bad += 1
                print(f"  PURE-COL FAILS TO VANISH n={n} A={A}")
        for T in itertools.chain.from_iterable(
                itertools.combinations(range(q), r) for r in range(q + 1)):
            S = [(j * q + c * p) % n for c in T for j in range(p)]
            if not vanishes(S, n, phi):
                bad += 1
                print(f"  PURE-ROW FAILS TO VANISH n={n} T={T}")
        # (b) random non-pure subsets must NOT vanish
        for _ in range(samples):
            S = [e for e in range(n) if rng.random() < rng.choice((0.2, 0.5, 0.8))]
            if not is_pure(S, p, q):
                if vanishes(S, n, phi):
                    bad += 1
                    print(f"  NON-PURE VANISHES n={n} S={S}")
        # (c) adversarial: pure form with one element toggled must not vanish
        for _ in range(2000):
            A = [j for j in range(p) if rng.random() < 0.5]
            S = set((j * q + c * p) % n for j in A for c in range(q))
            e = rng.randrange(n)
            S2 = S ^ {e}
            if not is_pure(S2, p, q) and vanishes(S2, n, phi):
                bad += 1
                print(f"  TOGGLED PURE VANISHES n={n} S={sorted(S2)}")
        print(f"  n={n}={p}*{q}: forms+{samples} random+2000 toggled, mismatches={bad}")
    return bad

def check_rigidity(p):
    """Subsets of mu_p with equal sums are equal or {empty, full}."""
    phi = Poly(cyclotomic_poly(p, x), x, domain=ZZ)
    bad = 0
    sums = {}
    for mask in range(2 ** p):
        S = tuple(e for e in range(p) if (mask >> e) & 1)
        # canonical form of sum: indicator poly mod Phi_p
        coeffs = [0] * p
        for e in S:
            coeffs[e] = 1
        key = tuple(Poly(list(reversed(coeffs)), x, domain=ZZ).rem(phi).all_coeffs())
        sums.setdefault(key, []).append(S)
    for key, fam in sums.items():
        if len(fam) > 1:
            ok = (len(fam) == 2 and set(fam) == {(), tuple(range(p))})
            if not ok:
                bad += 1
                print(f"  RIGIDITY FAILS p={p}: {fam[:4]}")
    print(f"  rigidity p={p}: 2^{p} subsets, {len(sums)} distinct sums, violations={bad}")
    return bad

def main():
    total = 0
    print("[rigidity dichotomy at primes]")
    for p in (3, 5, 7, 11, 13):
        total += check_rigidity(p)
    print("[pq classification]")
    total += check_pq(2, 3, exhaustive=True)
    total += check_pq(3, 5, exhaustive=True)
    total += check_pq(5, 7, exhaustive=False)
    print(f"TOTAL violations: {total}")
    return 0 if total == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
