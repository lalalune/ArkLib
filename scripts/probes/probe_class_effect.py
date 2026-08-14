#!/usr/bin/env python3
"""
probe_class_effect.py — falsification probe for the O39 class-group hypothesis.

Hypothesis (O39): transition-zone collisions are box-short generators of ideals
(alpha) = a*P (P a degree-1 prime above p, N(a) = cofactor). At m = 32,
h(Q(zeta_32)) = 1 — every a*P is principal, no class obstruction. At m = 64,
h(Q(zeta_64)) = 17 — a collision additionally forces a*P PRINCIPAL, i.e. the class
[P] = [a]^{-1} must be hit by a small-norm ideal class, a 1/h-flavored thinning.

Experiment (layer r = 5, both m): ladder of primes p ≡ 1 (mod m) at matched ratios
u = log2(p)/log2(T(m,5)), T(m,5) = 20^{m/4}. At each rung: exact e1-image on
5-subsets (pattern enumeration), deficiency vs N0(m,5), and for deficient rungs the
full collision-relation extraction (distinct difference vectors, supports, exact
Bareiss cofactors N(alpha)/p).

Readouts:
  (1) deficiency curves image/N0 vs u for h=1 vs h=17 (qualitative; m changes more
      than h, so this alone is suggestive only);
  (2) THE SHARP READ: the cofactor spectrum at m=64. All cofactors must be norms of
      ideals; the hypothesis predicts they are norms of ideals a with a*P principal.
      Pure 2-power cofactors are norms of (1-zeta)^j (principal, since (1-zeta) is) —
      those are always allowed. Cofactors that are norms of non-principal small
      ideals appearing would FALSIFY the principality mechanism (or reveal unit
      subtleties); their absence is consistent with it.
N0(32,5) = 144,288;  N0(64,5) = 6,483,776.  Deterministic; exit 0 = ran to completion
(this probe MEASURES; its only hard checks are bookkeeping identities). Rungs with
p >= 2^62 are skipped (int64 matmul range); the deficient region sits far below that.
"""
import itertools
import math
import sys
from collections import Counter

import numpy as np

FAIL = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n):
    if n < 2:
        return False
    for q in _MR_BASES:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def smallest_prime_1mod(m, lo):
    c = ((lo + m - 1) // m) * m + 1
    while not is_prime(c):
        c += m
    return c


def order_m_gen(p, m):
    x = 3
    while True:
        g = pow(x, (p - 1) // m, p)
        if g != 1 and pow(g, m // 2, p) != 1:
            return g
        x += 1


def patterns_layer(m, r):
    """Admissible eps for layer r as int8 (N, m//2), enumeration order fixed."""
    half = m // 2
    out = []
    smax = min(r, m - r)
    for s in range(r % 2, smax + 1, 2):
        for supp in itertools.combinations(range(half), s):
            for signs in itertools.product((1, -1), repeat=s):
                e = np.zeros(half, dtype=np.int8)
                e[list(supp)] = signs
                out.append(e)
    return np.stack(out)


def exact_abs_norm(c, half):
    n = half
    M = [[0] * n for _ in range(n)]
    for j, cj in enumerate(int(v) for v in c):
        if cj == 0:
            continue
        for k in range(n):
            idx, sgn = j + k, 1
            while idx >= n:
                idx -= n
                sgn = -sgn
            M[idx][k] += sgn * cj
    prev, sign = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for s in range(k + 1, n):
                if M[s][k] != 0:
                    M[k], M[s] = M[s], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return abs(sign * M[n - 1][n - 1])


def image_and_relations(p, m, r, P):
    half = m // 2
    g = order_m_gen(p, m)
    pows = np.array([pow(g, j, p) for j in range(half)], dtype=np.int64)
    vals = np.zeros(len(P), dtype=np.int64)
    for i0 in range(0, len(P), 1 << 20):
        vals[i0:i0 + (1 << 20)] = (P[i0:i0 + (1 << 20)].astype(np.int64) @ pows) % p
    order = np.argsort(vals, kind="stable")
    sv = vals[order]
    runs = np.flatnonzero(np.diff(sv) != 0)
    starts = np.concatenate(([0], runs + 1))
    ends = np.concatenate((runs + 1, [len(sv)]))
    distinct = len(starts)
    lost = len(P) - distinct
    rels = Counter()
    for s0, e0 in zip(starts, ends):
        if e0 - s0 == 1:
            continue
        idx = order[s0:e0]
        for a, b in itertools.combinations(idx, 2):
            c = (P[a].astype(np.int16) - P[b].astype(np.int16))
            nz = c[c != 0]
            if len(nz) == 0:
                continue
            key = tuple(c) if nz[0] > 0 else tuple(-c)
            rels[key] += 1
    return distinct, lost, rels


def run_ladder(m, r, ratios):
    half = m // 2
    T = 20 ** (m // 4)
    P = patterns_layer(m, r)
    n0 = len(P)
    print(f"\n== m={m} (h(Q(zeta_{m})) = {1 if m <= 32 else 17}), r={r}: N0 = {n0:,}, "
          f"T(m,5) = 20^{m//4} ≈ 2^{math.log2(T):.2f} ==")
    print(f"{'u=lg p/lg T':>12} {'p':>22} {'image/N0':>10} {'lost':>8} {'#rel':>6}  cofactors (support: N/p)")
    for u in ratios:
        p = smallest_prime_1mod(m, int(2 ** (u * math.log2(T))))
        if p >= (1 << 62):
            print(f"{u:>12.2f} {p:>22,}   [skipped: p >= 2^62, int64 matmul range]")
            continue
        distinct, lost, rels = image_and_relations(p, m, r, P)
        cof_summary = ""
        if rels:
            cofs = Counter()
            for c_key in list(rels)[:200]:
                t = sum(1 for v in c_key if v)
                N = exact_abs_norm(c_key, half)
                q, rem = divmod(N, p)
                cofs[(t, q if rem == 0 else f"NOT-DIV!")] += 1
            cof_summary = "  " + ", ".join(f"{t}:{q}×{ct}" for (t, q), ct in sorted(cofs.items())[:8])
            bad = [k for k in cofs if isinstance(k[1], str)]
            if bad:
                check(f"m={m} u={u}: all relations divisible by p", False, str(bad))
        print(f"{u:>12.2f} {p:>22,} {distinct / n0:>10.6f} {lost:>8,} {len(rels):>6,}{cof_summary}")
    return n0


if __name__ == "__main__":
    # matched ratios; m=32 rung at u covers p ~ 2^{34.6u}, m=64 rung covers p ~ 2^{69.15u}
    ratios = (0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.97)
    n032 = run_ladder(32, 5, ratios)
    n064 = run_ladder(64, 5, ratios)
    check("N0 bookkeeping", n032 == 144_288 and n064 == 6_483_776, f"{n032:,} / {n064:,}")
    print(f"\nfailures: {FAIL or 'none'}")
    sys.exit(1 if FAIL else 0)
