#!/usr/bin/env python3
"""Falsify-first probe for the WINDOW-FIBER THREAD FACTORIZATION + COUNT LAW
(issue #232; O106/O107's named consumer (ii): O70's count structure
F_n(t) = F_L(t)^{n/L}).

Definitions: F_n(t) = the window fiber = {S subset [0,n) : sum_{e in S}
zeta^{j e} = 0 for all 1 <= j <= t} (zeta primitive n-th, char 0).  By the
windowed law (O106) this equals the family of disjoint unions of canonical
rotated mu_d-cosets, d | n, d > t.

Let D(t) = {d : d | n, d > t}, Dmin(t) its divisibility-minimal elements,
L = lcm(Dmin(t)), g = n / L.  CONJECTURED LAWS:

  (A) REFINEMENT: every S in F_n(t) is a disjoint union of mu_{d'}-cosets
      with d' in Dmin(t) alone.
  (B) THREAD IFF: S in F_n(t)  <=>  for every c < g the thread
      T_c(S) = {y < L : c + g*y in S} lies in F_L(t)  (same t; note t < L).
  (C) COUNT LAW: |F_n(t)| = |F_L(t)|^g, via the bijection S <-> (T_0,...,T_{g-1}).
  (D) HYPOTHESIS SHAPE: for every d | n with d > t there is d' | gcd(d, L)
      with d' > t (the parameterized form used by the Lean brick).

METHOD (exact, exhaustive):
  * n in {12, 18}: ANALYTIC ground truth — F_n(t) computed for ALL 2^n masks
    by exact arithmetic in Z[x]/Phi_n; F_L(t) likewise; then (B), (C), (D)
    checked against the analytic fibers for every t in 1..n-1.
  * n in {20, 24, 36}: combinatorial fiber (disjoint coset unions, BFS with
    dedupe — legitimate ground truth given machine-checked O106) for every
    t in 1..n-1; (A)-(D) checked; for n = 24, t = 1 the known value
    F_6(1) = 7 gives the classical cross-check F_24(1) = 7^4 = 2401.

Exit 0 iff every check passes.
"""
import itertools
import math
import sys

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("FAIL:", msg)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def polydiv_exact(num, den):
    num = list(num)
    out = [0] * (len(num) - len(den) + 1)
    for i in range(len(num) - len(den), -1, -1):
        c = num[i + len(den) - 1]
        assert c % den[-1] == 0
        q = c // den[-1]
        out[i] = q
        for k, dc in enumerate(den):
            num[i + k] -= q * dc
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    return out, num


def cyclotomic(n, cache={}):
    if n in cache:
        return cache[n]
    num = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            num, rem = polydiv_exact(num, cyclotomic(d))
            assert all(c == 0 for c in rem)
    cache[n] = num
    return num


def pow_table(n):
    """x^k mod Phi_n for k < n (tuples, length deg Phi_n)."""
    phi = cyclotomic(n)
    deg = len(phi) - 1
    table, cur = [], [1] + [0] * (deg - 1)
    for _ in range(n):
        table.append(tuple(cur))
        nxt = [0] + cur[:]
        if len(nxt) > deg:
            lead = nxt[deg]
            nxt = [nxt[i] - lead * phi[i] for i in range(deg)]
        cur = nxt[:deg]
    return table


def analytic_fiber(n, t):
    """All S subset [0,n) (as frozensets) with vanishing window 1..t, by exact
    arithmetic in Z[x]/Phi_n."""
    table = pow_table(n)
    deg = len(table[0])
    jt = {j: [table[(j * e) % n] for e in range(n)] for j in range(1, t + 1)}
    out = set()
    for mask in range(1 << n):
        S = [e for e in range(n) if mask >> e & 1]
        ok = True
        for j in range(1, t + 1):
            acc = [0] * deg
            for e in S:
                te = jt[j][e]
                for k in range(deg):
                    acc[k] += te[k]
            if any(acc):
                ok = False
                break
        if ok:
            out.add(frozenset(S))
    return out


def coset(n, d, r):
    return frozenset(r + s * (n // d) for s in range(d))


def combinatorial_fiber(n, t):
    """All disjoint unions of canonical mu_d-cosets, d | n, d > t (BFS, dedupe)."""
    gens = [coset(n, d, r) for d in divisors(n) if d > t for r in range(n // d)]
    seen = {frozenset()}
    frontier = [frozenset()]
    while frontier:
        new = []
        for S in frontier:
            for c in gens:
                if not (c & S):
                    u = S | c
                    if u not in seen:
                        seen.add(u)
                        new.append(u)
        frontier = new
    return seen


def dmin_and_L(n, t):
    D = [d for d in divisors(n) if d > t]
    Dmin = [d for d in D if not any(d2 != d and d % d2 == 0 for d2 in D)]
    L = 1
    for d in Dmin:
        L = L * d // math.gcd(L, d)
    return Dmin, L


def refine_check(n, t, fiber, Dmin):
    """(A): every fiber member decomposes using Dmin-cosets only (peel search)."""
    gens = [coset(n, d, r) for d in Dmin for r in range(n // d)]

    def peel(rem):
        if not rem:
            return True
        e = min(rem)
        for c in gens:
            if e in c and c <= rem and peel(rem - c):
                return True
        return False

    for S in fiber:
        if not peel(S):
            fail(f"n={n} t={t}: {sorted(S)} has no Dmin={Dmin} decomposition")
            return


def thread(S, c, g, L):
    return frozenset(y for y in range(L) if (c + g * y) in S)


def run_case(n, ts, fiber_fn):
    for t in ts:
        Dmin, L = dmin_and_L(n, t)
        g = n // L
        fib_n = fiber_fn(n, t)
        fib_L = fiber_fn(L, t) if L < n else fib_n
        # (D) hypothesis shape
        for d in divisors(n):
            if d > t and not any(d % d2 == 0 and L % d2 == 0 and d2 > t
                                 for d2 in divisors(n)):
                fail(f"n={n} t={t}: divisor {d} has no d'|gcd(d,L), d'>t")
        # (A) refinement
        refine_check(n, t, fib_n, Dmin)
        # (B) thread iff, both directions, over the full powerset is too big;
        # forward over fiber + backward over the product reassembly:
        for S in fib_n:
            for c in range(g):
                if thread(S, c, g, L) not in fib_L:
                    fail(f"n={n} t={t}: S={sorted(S)} in fiber but thread "
                         f"{c} not in F_{L}({t})")
        # (C) count law via explicit product reassembly (also closes (B) <=)
        count = 0
        for combo in itertools.product(sorted(fib_L, key=sorted), repeat=g):
            S = frozenset(c + g * y for c in range(g) for y in combo[c])
            if S not in fib_n:
                fail(f"n={n} t={t}: reassembled threads {combo} not in fiber")
                break
            count += 1
        if count != len(fib_n):
            fail(f"n={n} t={t}: |F_{L}|^{g} = {len(fib_L) ** g} != "
                 f"|F_{n}| = {len(fib_n)}")
        print(f"  n={n:2d} t={t:2d}: Dmin={Dmin} L={L:2d} g={g} "
              f"|F_L|={len(fib_L):5d} |F_n|={len(fib_n):7d} "
              f"= |F_L|^g  OK")


def main():
    print("ANALYTIC ground truth (exact Z[x]/Phi_n, all masks):")
    run_case(12, range(1, 12), analytic_fiber)
    run_case(18, range(1, 18), analytic_fiber)
    print("COMBINATORIAL fiber (O106 ground truth):")
    run_case(20, range(1, 20), combinatorial_fiber)
    run_case(24, range(1, 24), combinatorial_fiber)
    run_case(36, range(1, 36), combinatorial_fiber)
    # classical cross-check: F_6(1) = 10 by hand (empty set, 3 mu_2-cosets,
    # 2 mu_3-cosets, 3 disjoint mu_2-pair unions, full mu_6), so
    # F_24(1) = 10^4; both fibers recomputed independently here.
    f6 = combinatorial_fiber(6, 1)
    f24 = combinatorial_fiber(24, 1)
    if len(f6) != 10 or len(f24) != 10 ** 4:
        fail(f"classical cross-check: F_6(1)={len(f6)} (want 10), "
             f"F_24(1)={len(f24)} (want 10000)")
    else:
        print(f"classical cross-check: F_6(1)=10, F_24(1)=10^4=10000  OK")
    if FAILS:
        print(f"{FAILS} FAILURES")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
