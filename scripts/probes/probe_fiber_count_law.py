#!/usr/bin/env python3
"""Probe for O109 (issue #232): the window fiber-count law F_n(t) ~= F_m(t)^(n/m).

By O106 (windowed_two_prime), the window fiber F_n(t) := {S subset [0,n) :
sum_{e in S} zeta^{je} = 0 for 1 <= j <= t} EQUALS the family of disjoint unions
of canonical rotated mu_d-cosets cosetOf(n,d,r) = {r + s*(n/d) : s < d}, r < n/d,
with d | n and d > t.  So the fiber-count law is PURE COMBINATORICS of coset
unions; no roots of unity appear anywhere below.

THE LAW (O70, 'F_n(t) ~= F_lcm(Dmin)(t)^(n/lcm) verified 25/25'):
  Dmin := divisibility-minimal divisors of n exceeding t,
  m    := lcm(Dmin)   (m | n),  g := n/m.
  Block structure: block c (0 <= c < g) is {e in [0,n) : e % g == c}; the trace
  of S on block c is  T_c(S) := { e // g : e in S, e % g == c }  (a subset of
  [0,m)).  CLAIM (set-level bijection):
      S in F_n(t)  <=>  for every c < g,  T_c(S) in F_m(t),
  and S |-> (T_0(S), ..., T_{g-1}(S)) is a bijection F_n(t) -> F_m(t)^g.
  Hence |F_n(t)| = |F_m(t)|^(n/m).

  Key structural lemma behind it: the trace of a mu_d-coset (a full residue
  class mod n/d) on a block is empty or a full residue class mod m/gcd(d,m) in
  [0,m), i.e. a mu_{gcd(d,m)}-coset at level m; and gcd(d,m) > t because every
  divisor d|n with d>t is a multiple of some element of Dmin, which divides m.

This probe verifies, exhaustively at n in {12, 18, 24, 36} and ALL t in [1, n):
  (1) the Dmin / lcm computation and the key gcd inequality
      (forall d|n, d>t: gcd(d,m) > t);
  (2) |F_n(t)| including reproducing O70's |F_36(t)| plateau table
      10^6, 22^3, 1036, 100, 22, 10, 4, 2;
  (3) the trace direction: EVERY S in F_n(t) has all g traces in F_m(t);
  (4) the count law |F_n(t)| == |F_m(t)|^g  (with (3) and injectivity of the
      total trace map this forces the full set-level bijection);
  (5) the lift direction on samples: assembled tuples of F_m(t) members land in
      F_n(t) (sampled when the product is large, exhaustive when small);
  (6) the coset-trace lemma: every trace of every allowed coset on every block
      is empty or a mu_{gcd(d,m)}-coset at level m.
"""

from math import gcd, lcm
from itertools import product
import random

random.seed(232109)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def cosets(n, t):
    """All canonical rotated mu_d-cosets with d|n, d>t, as bitmasks over [0,n)."""
    out = []
    for d in divisors(n):
        if d > t:
            k = n // d
            for r in range(k):
                mask = 0
                for s in range(d):
                    mask |= 1 << (r + s * k)
                out.append((d, r, mask))
    return out


def fiber(n, t):
    """F_n(t) as a set of bitmasks: all disjoint unions of allowed cosets (BFS)."""
    cs = [mask for (_, _, mask) in cosets(n, t)]
    fam = {0}
    frontier = [0]
    while frontier:
        nxt = []
        for S in frontier:
            for C in cs:
                if S & C == 0:
                    U = S | C
                    if U not in fam:
                        fam.add(U)
                        nxt.append(U)
        frontier = nxt
    return fam


def dmin_and_m(n, t):
    big = [d for d in divisors(n) if d > t]
    dmin = [d for d in big if all(not (d2 != d and d % d2 == 0) for d2 in big)]
    m = lcm(*dmin) if dmin else 1
    return dmin, m


def traces(S, n, m):
    """The g = n/m block traces of bitmask S over [0,n), as bitmasks over [0,m)."""
    g = n // m
    out = [0] * g
    for e in range(n):
        if S >> e & 1:
            out[e % g] |= 1 << (e // g)
    return out


def assemble(tup, n, m):
    g = n // m
    S = 0
    for c, T in enumerate(tup):
        for f in range(m):
            if T >> f & 1:
                S |= 1 << (c + f * g)
    return S


def is_coset_at_level(T, m, allowed_d):
    """Is bitmask T over [0,m) empty or a full residue class mod m/u with u in allowed_d?"""
    if T == 0:
        return True
    els = [f for f in range(m) if T >> f & 1]
    u = len(els)
    if u not in allowed_d:
        return False
    k = m // u
    r = els[0] % k
    return all(f % k == r for f in els) and set(els) == {r + s * k for s in range(u)}


def main():
    o70_table = {36: {1: 10 ** 6, 2: 22 ** 3, 3: 1036, 4: 100, 6: 22, 9: 10, 12: 4, 18: 2}}
    fibers = {}  # (n, t) -> family
    all_ok = True

    for n in [12, 18, 24, 36]:
        print(f"== n = {n}, divisors {divisors(n)}")
        # fibers plateau between divisors: compute once per plateau, reuse
        plateau_reps = {}
        for t in range(1, n):
            big = tuple(d for d in divisors(n) if d > t)
            if big not in plateau_reps:
                plateau_reps[big] = fiber(n, t)
            fibers[(n, t)] = plateau_reps[big]

        for t in range(1, n):
            F = fibers[(n, t)]
            dmin, m = dmin_and_m(n, t)
            g = n // m

            # (1) key gcd inequality
            key = all(gcd(d, m) > t for d in divisors(n) if d > t)

            # (2) O70 table reproduction
            tbl_ok = True
            if n in o70_table and t in o70_table[n]:
                tbl_ok = len(F) == o70_table[n][t]

            # need F_m(t); m | n and m <= n, compute (cheap: plateaus again)
            if (m, t) not in fibers:
                fibers[(m, t)] = fiber(m, t)
            Fm = fibers[(m, t)]

            # (3) trace direction, exhaustive over F_n(t)
            trace_ok = all(all(T in Fm for T in traces(S, n, m)) for S in F)

            # (4) the count law
            count_ok = len(F) == len(Fm) ** g

            # (5) lift direction: exhaustive if small, else 2000 random tuples
            if len(Fm) ** g <= 20000:
                tuples = product(Fm, repeat=g)
            else:
                Fml = list(Fm)
                tuples = (tuple(random.choice(Fml) for _ in range(g)) for _ in range(2000))
            lift_ok = all(assemble(tup, n, m) in F for tup in tuples)

            # (6) coset-trace lemma
            allowed = {d for d in divisors(m) if d > t}
            coset_ok = all(
                is_coset_at_level(T, m, allowed)
                for (_, _, C) in cosets(n, t) for T in traces(C, n, m))

            ok = key and tbl_ok and trace_ok and count_ok and lift_ok and coset_ok
            all_ok &= ok
            flag = "OK " if ok else "FAIL"
            print(f"  t={t:2d}  Dmin={dmin!s:>14}  m={m:2d} g={g:2d}  "
                  f"|F_n|={len(F):8d} |F_m|^g={len(Fm)}^{g}={len(Fm) ** g:8d}  "
                  f"key={key} tbl={tbl_ok} trace={trace_ok} count={count_ok} "
                  f"lift={lift_ok} cosetTrace={coset_ok}  [{flag}]")

    print()
    print("ALL CHECKS PASS" if all_ok else "SOME CHECK FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
