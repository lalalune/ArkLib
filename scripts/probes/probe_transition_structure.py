#!/usr/bin/env python3
"""
probe_transition_structure.py — the STRUCTURE of modular collisions in the transition
zone N0 <~ p < T(m,r). Companion to EffectivePerPrimeExactness.md section 4 (O38).

E2(c) (support-graded threshold) makes sharp falsifiable predictions about WHICH
collisions can occur below T:

  every collision relation c = eps - eps' (a difference of admissible patterns with
  equal e1-value mod p) must have |supp(c)| > t whenever p > (4t)^{m/4}.

Tested here by EXHAUSTIVE collision extraction:

  P1 (m=16, r=9, p=205,553 — the exact onset prime):   (4*5)^4 = 160,000 < p < (4*6)^4
        => every relation has support >= 6 (of 8 slots).
  P2 (m=16, r=5, p=43,793 — the layer-5 onset prime):  (4*3)^4 = 20,736 < p < (4*4)^4
        => every relation has support >= 4.
  P3 (m=32, r=17, p=BabyBear=2013265921):              12^8 ~ 2^28.7 < p < 16^8 = 2^32
        => every relation has support >= 4.
       Also re-derives the exact lost-value count 45,952 from the collision classes.

Additionally measured (data, not theorems): the distinct-relation count, the support
histogram, the per-relation pair-multiplicity vs the proven cap 2^t * 3^{m/2-t}, and
exact integer norms N(c) (Bareiss on the negacyclic multiplication matrix) for sampled
relations — by construction p | N(c); the cofactor N(c)/p calibrates how deep into the
norm range the realized relations sit. Deterministic. Exit 0 iff all predictions hold.
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


def order_m_gen(p, m):
    assert (p - 1) % m == 0
    x = 3
    while True:
        g = pow(x, (p - 1) // m, p)
        if g != 1 and pow(g, m // 2, p) != 1:
            return g
        x += 1


def s_range(m, r):
    smax = min(r, m - r)
    return range(r % 2, smax + 1, 2)


def exact_abs_norm(c, half):
    """|N_{Q(zeta_{2*half*2})/Q}| of sum c_j zeta^j via |det| of multiplication on
    Z[x]/(x^half + 1), fraction-free Bareiss (exact integers)."""
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


def collision_relations(p, m, r, sample_norms=12):
    """Exhaustively extract all same-layer collision pairs at (p, m, r) via indexed
    MITM; return (lost_count, list of (support, multiplicity) per distinct |relation|,
    sampled exact norms). Relations deduped up to global sign."""
    half = m // 2
    hh = half // 2
    g = order_m_gen(p, m)
    pows = [pow(g, j, p) for j in range(half)]

    pats = np.array(list(itertools.product((-1, 0, 1), repeat=hh)), dtype=np.int8)
    npat = len(pats)  # 3^hh
    powL = np.array(pows[:hh], dtype=np.int64)
    powR = np.array(pows[hh:], dtype=np.int64)
    valL = (pats.astype(np.int64) @ powL) % p
    valR = (pats.astype(np.int64) @ powR) % p
    sL = np.count_nonzero(pats, axis=1).astype(np.int16)
    sR = sL.copy()

    smax = min(r, m - r)
    par = r % 2

    rows_v, rows_l, rows_r = [], [], []
    for i0 in range(0, npat, 512):
        a = valL[i0:i0 + 512][:, None] + valR[None, :]
        a %= p
        stot = sL[i0:i0 + 512][:, None] + sR[None, :]
        mask = ((stot & 1) == par) & (stot <= smax)
        li, ri = np.nonzero(mask)
        rows_v.append(a[li, ri].astype(np.uint64))
        rows_l.append((li + i0).astype(np.uint32))
        rows_r.append(ri.astype(np.uint32))
    V = np.concatenate(rows_v)
    L = np.concatenate(rows_l)
    R = np.concatenate(rows_r)
    total = len(V)

    order = np.argsort(V, kind="stable")
    V, L, R = V[order], L[order], R[order]
    distinct = len(np.unique(V))
    lost = total - distinct

    # collision classes = runs of equal V
    runs = np.flatnonzero(np.diff(V) != 0)
    starts = np.concatenate(([0], runs + 1))
    ends = np.concatenate((runs + 1, [total]))
    rel_counter = Counter()
    for s0, e0 in zip(starts, ends):
        k = e0 - s0
        if k == 1:
            continue
        idx = range(s0, e0)
        for i, jj in itertools.combinations(idx, 2):
            c = np.zeros(half, dtype=np.int16)
            c[:hh] = pats[L[i]] - pats[L[jj]]
            c[hh:] = pats[R[i]] - pats[R[jj]]
            if not c.any():
                continue  # same pattern via different half-split cannot happen (split is canonical)
            key = tuple(c) if (c[c != 0][0] > 0) else tuple(-c)  # sign-normalize
            rel_counter[key] += 1

    supports = Counter()
    for c_key, mult in rel_counter.items():
        t = sum(1 for v in c_key if v)
        supports[t] += 1
    norms = []
    for c_key, mult in sorted(rel_counter.items(), key=lambda kv: -kv[1])[:sample_norms]:
        N = exact_abs_norm(c_key, half)
        norms.append((sum(1 for v in c_key if v), mult, N, N % p == 0, N // p))
    return total, distinct, lost, rel_counter, supports, norms


def run_case(tag, p, m, r, predicted_min_support, expected_lost=None):
    print(f"\n== {tag}: p={p:,} (≈2^{math.log2(p):.2f}), m={m}, r={r} ==")
    t_pred = predicted_min_support
    total, distinct, lost, rels, supports, norms = collision_relations(p, m, r)
    print(f"   patterns={total:,} distinct={distinct:,} lost={lost:,}; "
          f"distinct relations (±): {len(rels):,}; support histogram: {dict(sorted(supports.items()))}")
    if expected_lost is not None:
        check(f"{tag}: lost-value count matches prior probe", lost == expected_lost,
              f"{lost} vs {expected_lost}")
    min_sup = min(supports) if supports else None
    check(f"{tag}: E2(c) support floor — all relations have support >= {t_pred}",
          min_sup is None or min_sup >= t_pred, f"min support = {min_sup}")
    half = m // 2
    mult_viol = []
    for c_key, mult in rels.items():
        t = sum(1 for v in c_key if v)
        if mult > (2 ** t) * (3 ** (half - t)):
            mult_viol.append((c_key, mult))
    check(f"{tag}: multiplicity cap 2^t*3^(m/2-t) holds for every relation",
          not mult_viol, f"violations: {len(mult_viol)}")
    div_ok = all(d for (_, _, _, d, _) in norms)
    check(f"{tag}: sampled relations all satisfy p | N(c) (exact Bareiss)", div_ok)
    for t, mult, N, _, cof in norms[:6]:
        print(f"     relation support={t} pairs={mult:>6,}  N = p × {cof:,}  "
              f"(log2 N = {math.log2(N):.2f}, bound (4t)^{{m/4}} = {math.log2((4*t)**(half//2)):.2f})")
    return supports


if __name__ == "__main__":
    # m=16 boundary primes (exhaustive pattern space: 3281/2256 patterns)
    run_case("P1 onset(16,9)", 205_553, 16, 9, 6)
    run_case("P2 onset(16,5)", 43_793, 16, 5, 4)
    # BabyBear m=32 (21.5M patterns; ~1-2 min, ~1.5 GB peak)
    run_case("P3 BabyBear(32,17)", 15 * (1 << 27) + 1, 32, 17, 4, expected_lost=45_952)
    print(f"\nfailures: {FAIL or 'none'}")
    sys.exit(1 if FAIL else 0)
