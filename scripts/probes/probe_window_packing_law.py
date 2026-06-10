#!/usr/bin/env python3
"""Falsify-first probe for THE 0/1 PACKING LAW (issue #232; the open surface
named by O112: which masses are realizable by window-vanishing 0/1 sets).

TESTED CONJECTURE (the two-sided span law) and its REFUTATION: for n
two-prime-smooth, t < n, D(t) = {d : d | n, d > t}, is the realizable 0/1
mass set

    M_n(t) = { mu in [0, n] : mu in NN-span(D(t))  AND  n - mu in NN-span(D(t)) } ?

NECESSITY holds (O107 span + COMPLEMENT CLOSURE: the full set [0,n) is itself
window-vanishing, so S in F_n(t) iff its complement is).  SUFFICIENCY IS
FALSE: at n = 36, t = 3, the mass 13 = 9 + 4 is two-sided (23 = 9+4+4+6) but
its ONLY divisor representation is {9, 4}, and a mu_9-coset (step 4) and a
mu_4-coset (step 9) have COPRIME steps, hence always intersect (CRT) — 13 is
unrealizable.  The probe verifies necessity everywhere, locates ALL
two-sided-but-unrealizable masses (the CRT/packing stratum), and measures the
naive tiling claim (also false: {4,3,3,2} at n = 12 — parity invariant).

CHECKS (exhaustive, pure coset combinatorics — legitimate by O106; exit 0 iff
all pass):
  (1) COMPLEMENT CLOSURE: F_n(t) is closed under complement in [0,n)
      for n in {12, 18, 20, 24, 36}, all t in [1, n).
  (2) NECESSITY: M_n(t) subset of the two-sided span set, same range; report
      (do not fail) the two-sided masses that are NOT realizable — the
      CRT/packing stratum, with the (36, 3, 13) instance REQUIRED present.
  (3) TILING (data, capped): for n in {12, 18, 20, 24}, all t, which divisor
      multisets summing to n tile [0,n) — counts reported, no hard check
      (the naive claim is known false).
  (4) the n = 18, t = 1, mass 17 obstruction reproduces as 18 - 17 = 1
      not in span.
"""
import sys
from functools import lru_cache

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("FAIL:", msg)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def coset(n, d, r):
    return frozenset(r + s * (n // d) for s in range(d))


def fiber(n, t):
    """All disjoint unions of canonical mu_d-cosets, d | n, d > t (BFS)."""
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


def span_set(ds, bound):
    reach = {0}
    frontier = [0]
    while frontier:
        new = []
        for v in frontier:
            for d in ds:
                u = v + d
                if u <= bound and u not in reach:
                    reach.add(u)
                    new.append(u)
        frontier = new
    return reach


def all_multisets(ds, total):
    """All multisets over ds (sorted desc) with the given total."""
    ds = sorted(ds, reverse=True)

    def rec(i, rem):
        if rem == 0:
            yield []
            return
        if i == len(ds):
            return
        d = ds[i]
        for k in range(rem // d, -1, -1):
            for rest in rec(i + 1, rem - k * d):
                yield [d] * k + rest

    yield from rec(0, total)


def tiles(n, multiset):
    """Backtracking exact cover of [0,n) by canonical cosets with the given
    size multiset."""
    from collections import Counter
    cnt = Counter(multiset)

    def rec(free, cnt):
        if not free:
            return True
        e = min(free)
        for d in list(cnt):
            if cnt[d] == 0:
                continue
            # the unique candidate coset of size d through e has base e % (n/d)
            c = coset(n, d, e % (n // d))
            if c <= free:
                cnt[d] -= 1
                if rec(free - c, cnt):
                    return True
                cnt[d] += 1
        return False

    return rec(frozenset(range(n)), cnt)


def run_case(n, do_tiling=False):
    crt_strata = {}
    for t in range(1, n):
        D = [d for d in divisors(n) if d > t]
        F = fiber(n, t)
        # (1) complement closure
        full = frozenset(range(n))
        for S in F:
            if (full - S) not in F:
                fail(f"n={n} t={t}: complement of {sorted(S)} not in fiber")
                break
        # (2) necessity + CRT stratum
        M = {len(S) for S in F}
        sp = span_set(D, n)
        pred = {m for m in sp if (n - m) in sp}
        extra = M - pred
        if extra:
            fail(f"n={n} t={t}: NECESSITY violated — realizable masses "
                 f"{sorted(extra)} outside the two-sided span")
        stratum = sorted(pred - M)
        if stratum:
            crt_strata[t] = stratum
        # (3) tiling data
        note = ""
        if do_tiling:
            ms_all = list(all_multisets(D, n))
            bad = sum(1 for ms in ms_all if not tiles(n, ms))
            note = f"  [tiling: {len(ms_all) - bad}/{len(ms_all)} multisets tile]"
        gap = f"  [CRT stratum: {stratum}]" if stratum else ""
        print(f"  n={n:2d} t={t:2d}: D={D} M={sorted(M)}{gap}{note}")
    return crt_strata


def main():
    strata36 = {}
    for n in (12, 18, 20, 24):
        run_case(n, do_tiling=True)
    strata36 = run_case(36)
    # the predicted CRT refutation instance
    if 13 in strata36.get(3, []):
        print("(36, t=3): mass 13 two-sided but UNREALIZABLE (CRT 9+4)  OK")
    else:
        fail(f"(36, t=3): expected 13 in the CRT stratum, got "
             f"{strata36.get(3, [])}")
    # (4) the O112 gap, explained
    sp = span_set([d for d in divisors(18) if d > 1], 18)
    if 17 in sp and 1 not in sp:
        print("n=18 t=1 mass-17 gap = complement obstruction (1 not in span)  OK")
    else:
        fail("n=18 t=1: expected 17 in span and 1 not in span")
    if FAILS:
        print(f"{FAILS} FAILURES")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
