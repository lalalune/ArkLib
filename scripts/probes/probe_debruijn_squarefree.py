#!/usr/bin/env python3
"""Falsify-first probe for the de Bruijn squarefree classification (#232, capstone step (3)).

Two claims, checked EXACTLY (integer polynomial arithmetic, no floats):

CLAIM A (the splice, n = p^a * q^b): a vanishing subset sum of mu_n has mu_q-shift
  invariant fiber sums over the CRT grid: A(i*q^(b-1) + s) independent of i < q, where
  A(c) = sum_j [(j,c) in G] * xi^j computed exactly in Z[x]/Phi_{p^a}(x), xi = zeta^{q^b}.
  (This is the composition of the landed CRTExponentGridSum.subset_sum_eq_grid_double_sum
  with CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers, with no hypothesis left.)

CLAIM B (the classification, squarefree n = p*q): a subset sum of mu_n vanishes IFF in
  CRT grid coordinates G = {(j,c) in [p)x[q) : (j*q + c*p) mod n in S} the index set is
    rows-form:    G = P x [0,q)   (all columns carry the same row pattern P), or
    columns-form: G = [0,p) x T   (every column is full or empty).
  This is de Bruijn (1953) / Lam-Leung specialized to squarefree two-prime n with 0/1
  coefficients: disjoint rotated packets + rows and columns always intersect => purity.

CONTROL: the purity claim must FAIL at non-squarefree n (n = 12: a mu_2-packet and a
  disjoint mu_3-packet mix), demonstrating squarefree-ness is load-bearing in CLAIM B
  while CLAIM A (slice invariance) still holds there.

Vanishing test: sum_{e in S} x^e === 0 mod Phi_n(x) over Z (exact division by the monic
cyclotomic polynomial; the n-th cyclotomic field relation ideal is (Phi_n)).

Exit 0 iff all checks pass.
"""

import itertools
import random
import sys

random.seed(232)

FAIL = 0


def fail(msg):
    global FAIL
    FAIL += 1
    print(f"  FAIL: {msg}")


# ---------- exact integer polynomial arithmetic (dense lists, index = degree) ----------

def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_mul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def poly_divmod(a, b):
    """Exact division of integer polys, b monic. Returns (quot, rem)."""
    a = a[:]
    assert b and b[-1] == 1, "divisor must be monic"
    db = len(b) - 1
    q = [0] * max(0, len(a) - db)
    while len(trim(a)) - 1 >= db and a:
        da = len(a) - 1
        c = a[-1]
        q[da - db] = c
        for i in range(db + 1):
            a[da - db + i] -= c * b[i]
        trim(a)
    return trim(q), trim(a)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


_CYCLO = {}


def cyclotomic(n):
    """Phi_n as integer coefficient list, via x^n - 1 = prod_{d|n} Phi_d."""
    if n in _CYCLO:
        return _CYCLO[n]
    num = [-1] + [0] * (n - 1) + [1]  # x^n - 1
    den = [1]
    for d in divisors(n):
        if d < n:
            den = poly_mul(den, cyclotomic(d))
    q, r = poly_divmod(num, den)
    assert r == [], f"cyclotomic({n}): nonexact division"
    _CYCLO[n] = q
    return q


def vanishes(S, n):
    """sum_{e in S} zeta^e == 0 for zeta a primitive n-th root, exactly."""
    p = [0] * n
    for e in S:
        p[e % n] += 1
    _, r = poly_divmod(trim(p[:]), cyclotomic(n))
    return r == []


# ---------- CRT grid bookkeeping (matches CRTExponentGridSum.gridMap: g(j,c) = j*M + c*N) ----------

def grid_set(S, N, M):
    """G = {(j,c) in [0,N)x[0,M) : (j*M + c*N) mod (N*M) in S}."""
    n = N * M
    Sset = set(e % n for e in S)
    return {(j, c) for j in range(N) for c in range(M) if (j * M + c * N) % n in Sset}


def rows_form(G, N, M):
    """All M columns carry the same row pattern."""
    cols = [frozenset(j for j in range(N) if (j, c) in G) for c in range(M)]
    return all(col == cols[0] for col in cols)


def cols_form(G, N, M):
    """Every column is full or empty."""
    for c in range(M):
        col = {j for j in range(N) if (j, c) in G}
        if col and len(col) != N:
            return False
    return True


def fiber_sum_reduced(G, N, M, c, PhiN):
    """A(c) = sum_j [(j,c) in G] x^j reduced mod Phi_N, as a tuple (exact elt of Z[zeta_N])."""
    p = [0] * N
    for j in range(N):
        if (j, c) in G:
            p[j] += 1
    _, r = poly_divmod(trim(p), PhiN)
    return tuple(r)


# ---------- CLAIM A: splice invariance at n = p^a q^b ----------

def check_claim_A(p, a, q, b, exhaustive_limit=2 ** 20, samples=4000):
    N, M, n = p ** a, q ** b, p ** a * q ** b
    Qp = q ** (b - 1)
    PhiN = cyclotomic(N)
    total = vcount = 0
    violations = 0
    noninv_nonvanishing = 0

    def check_one(S):
        nonlocal total, vcount, violations, noninv_nonvanishing
        total += 1
        G = grid_set(S, N, M)
        van = vanishes(S, n)
        inv = True
        for s in range(Qp):
            sums = [fiber_sum_reduced(G, N, M, i * Qp + s, PhiN) for i in range(q)]
            if any(x != sums[0] for x in sums[1:]):
                inv = False
                break
        if van:
            vcount += 1
            if not inv:
                violations += 1
                fail(f"A: vanishing S={sorted(S)} (n={n}) has non-invariant fiber sums")
        else:
            if not inv:
                noninv_nonvanishing += 1

    if 2 ** n <= exhaustive_limit:
        for bits in range(2 ** n):
            S = [e for e in range(n) if (bits >> e) & 1]
            check_one(S)
        mode = f"exhaustive 2^{n}"
    else:
        for _ in range(samples):
            S = [e for e in range(n) if random.random() < 0.5]
            check_one(S)
        # planted vanishing sets: unions of rotated full p-packets / q-packets
        for _ in range(samples // 4):
            S = set()
            for _ in range(random.randrange(1, 4)):
                if random.random() < 0.5:
                    r = random.randrange(n)
                    S |= {(r + t * (n // p)) % n for t in range(p)}
                else:
                    r = random.randrange(n)
                    S |= {(r + t * (n // q)) % n for t in range(q)}
            check_one(S)
        mode = f"sampled {total}"
    print(f"  A @ n={n}=({p}^{a})({q}^{b}): {mode}, vanishing={vcount}, "
          f"violations={violations}, non-invariant non-vanishing={noninv_nonvanishing}")
    return violations == 0


# ---------- CLAIM B: squarefree classification ----------

def check_claim_B(p, q, exhaustive_limit=2 ** 20, samples=20000):
    n = p * q
    total = vcount = 0
    mismatches = 0
    pure_nonvanishing = 0

    def check_one(S):
        nonlocal total, vcount, mismatches, pure_nonvanishing
        total += 1
        G = grid_set(S, p, q)
        van = vanishes(S, n)
        pure = rows_form(G, p, q) or cols_form(G, p, q)
        if van:
            vcount += 1
        if van != pure:
            mismatches += 1
            if van:
                fail(f"B: vanishing S={sorted(S)} (n={n}) is NEITHER rows- nor columns-form")
            else:
                pure_nonvanishing += 1
                fail(f"B: pure S={sorted(S)} (n={n}) does NOT vanish")

    if 2 ** n <= exhaustive_limit:
        for bits in range(2 ** n):
            S = [e for e in range(n) if (bits >> e) & 1]
            check_one(S)
        mode = f"exhaustive 2^{n}"
    else:
        for _ in range(samples):
            S = [e for e in range(n) if random.random() < 0.5]
            check_one(S)
        # adversarial: pure sets with one point toggled (must NOT vanish),
        # and genuine pure sets (must vanish)
        for _ in range(samples // 4):
            T = [c for c in range(q) if random.random() < 0.5]
            S = {(j * q + c * p) % n for j in range(p) for c in T}
            check_one(sorted(S))
            if S:
                S2 = set(S)
                e = random.randrange(n)
                S2.symmetric_difference_update({e})
                check_one(sorted(S2))
        mode = f"sampled {total}"
    print(f"  B @ n={n}={p}*{q}: {mode}, vanishing={vcount}, mismatches={mismatches}")
    return mismatches == 0


# ---------- CONTROL: purity fails at non-squarefree n ----------

def control_nonsquarefree():
    # n = 12 = 2^2 * 3: take the mu_2-packet {0,6} and the disjoint mu_3-packet {1,5,9}
    n, N, M = 12, 4, 3  # CRT split N = 2^2, M = 3
    S = [0, 6, 1, 5, 9]
    assert vanishes(S, n), "control: planted packet union must vanish"
    G = grid_set(S, N, M)
    pure = rows_form(G, N, M) or cols_form(G, N, M)
    if pure:
        fail("control: n=12 mixed packet union unexpectedly pure — control has no teeth")
    else:
        print(f"  control @ n=12: S={S} vanishes but is neither rows- nor columns-form "
              f"(squarefree-ness is load-bearing in CLAIM B)")
    # CLAIM A must still hold there: it is part of check_claim_A(2,2,3,1) exhaustively.


def main():
    print("probe_debruijn_squarefree: falsify-first for #232 de Bruijn step (3)")

    print("CLAIM B (classification, squarefree):")
    ok_B = True
    ok_B &= check_claim_B(2, 3)    # n=6  exhaustive
    ok_B &= check_claim_B(2, 5)    # n=10 exhaustive
    ok_B &= check_claim_B(3, 5)    # n=15 exhaustive
    ok_B &= check_claim_B(3, 7)    # n=21 sampled + adversarial
    ok_B &= check_claim_B(5, 7)    # n=35 sampled + adversarial

    print("CLAIM A (splice fiber-slice invariance, prime-power grids):")
    ok_A = True
    ok_A &= check_claim_A(2, 2, 3, 1)   # n=12 exhaustive
    ok_A &= check_claim_A(2, 1, 3, 2)   # n=18 exhaustive
    ok_A &= check_claim_A(3, 1, 5, 1)   # n=15 exhaustive (squarefree corner of A)
    ok_A &= check_claim_A(2, 2, 5, 1)   # n=20 exhaustive
    ok_A &= check_claim_A(3, 2, 2, 2)   # n=36 sampled + planted

    print("CONTROL (non-squarefree purity failure):")
    control_nonsquarefree()

    if FAIL == 0 and ok_A and ok_B:
        print("ALL CHECKS PASS (exit 0)")
        return 0
    print(f"{FAIL} FAILURES")
    return 1


if __name__ == "__main__":
    sys.exit(main())
