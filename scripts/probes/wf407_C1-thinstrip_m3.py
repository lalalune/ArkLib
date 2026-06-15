#!/usr/bin/env python3
"""
wf407 / C1-thinstrip companion -- FAST exact M3 (subgroup vs random) via
per-coordinate coincidence-pattern memoization.

For a triple of codewords (c1,c2,c3), the radius-w 3-ball intersection volume over
F_q^n depends ONLY on the multiset of per-coordinate "coincidence patterns": for
each coordinate i, the pattern is the set-partition of {1,2,3} induced by which of
c1[i],c2[i],c3[i] are equal, together with whether each block's value is "free"
(the DP only cares which centers SHARE a symbol -- a received symbol y_i either
hits one shared value or none).  We memoize the intersection on the sorted tuple
of pattern-codes, so identical triples are computed once.

Verdict context: PART C of the main probe already showed M2/M1 = 1 EXACTLY on the
whole strip (q~n*2^128).  Here we confirm the M3 ladder (M3/M2) ALSO pins at 1 on
the strip at small enumerable scale, and that the smooth-vs-random M3 gap is the
O133 q^{-4}-scale perturbation -- far too small to lift any moment lower bracket.
All exact integer arithmetic.
"""
from math import comb, isqrt
from fractions import Fraction
from functools import lru_cache
from collections import defaultdict
import itertools, random


def smooth_subgroup(p, n):
    def order(g):
        x = 1
        for k in range(1, p):
            x = (x * g) % p
            if x == 1: return k
        return p
    g = next(c for c in range(2, p) if order(c) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x); x = (x * h) % p
    return sorted(set(H))


def all_codewords(p, D, k):
    return [tuple(sum(coeffs[i] * pow(x, i, p) for i in range(k)) % p for x in D)
            for coeffs in itertools.product(range(p), repeat=k)]


def coord_pattern(symbols):
    """Canonical code for the equality-partition of a tuple of symbols.
    e.g. (a,a,b)->(0,0,1), (a,b,a)->(0,1,0), (a,b,c)->(0,1,2), (a,a,a)->(0,0,0)."""
    seen = {}
    out = []
    nxt = 0
    for s in symbols:
        if s not in seen:
            seen[s] = nxt; nxt += 1
        out.append(seen[s])
    return tuple(out)


# DP intersection for r centers given the per-coordinate equality-partition codes.
# For pattern with blocks B_1..B_m (m distinct values), a received symbol y_i can:
#   - equal block b's value: agrees with all centers in B_b, disagrees with others
#     (multiplicity 1 each)
#   - equal none of the present values: disagrees with all (multiplicity q-m)
def intersect_from_patterns(patterns, w, q, r):
    states = {(0,) * r: 1}
    for pat in patterns:
        m = max(pat) + 1
        # block members
        blocks = [[] for _ in range(m)]
        for idx, b in enumerate(pat):
            blocks[b].append(idx)
        trans = []
        for b in range(m):
            trans.append((set(blocks[b]), 1))
        other = q - m
        if other > 0:
            trans.append((set(), other))
        new = defaultdict(int)
        for st, cnt in states.items():
            for agree, mult in trans:
                ns = list(st); ok = True
                for j in range(r):
                    if j not in agree:
                        ns[j] += 1
                        if ns[j] > w: ok = False; break
                if ok:
                    new[tuple(ns)] += cnt * mult
        states = dict(new)
        if not states: return 0
    return sum(states.values())


def moments(p, D, k, w):
    cws = all_codewords(p, D, k)
    Q = len(cws)
    n = len(D)
    # M1
    M1 = 0
    vols1 = []
    for c in cws:
        pats = tuple(sorted(coord_pattern((c[i],)) for i in range(n)))
        v = intersect_from_patterns(pats, w, p, 1)
        vols1.append(v); M1 += v
    # memoized 2- and 3-fold
    memo2 = {}
    def vol2(i, j):
        pats = tuple(sorted(coord_pattern((cws[i][x], cws[j][x])) for x in range(n)))
        key = pats
        if key not in memo2:
            memo2[key] = intersect_from_patterns(pats, w, p, 2)
        return memo2[key]
    memo3 = {}
    def vol3(i, j, l):
        pats = tuple(sorted(coord_pattern((cws[i][x], cws[j][x], cws[l][x])) for x in range(n)))
        key = pats
        if key not in memo3:
            memo3[key] = intersect_from_patterns(pats, w, p, 3)
        return memo3[key]
    # M2 ordered
    M2 = 0
    for i in range(Q):
        M2 += vols1[i]
        for j in range(i + 1, Q):
            M2 += 2 * vol2(i, j)
    # M3 ordered
    M3 = 0
    for i in range(Q):
        M3 += vols1[i]
        for j in range(i + 1, Q):
            vij = vol2(i, j)
            M3 += 6 * vij
            for l in range(j + 1, Q):
                M3 += 6 * vol3(i, j, l)
    return M1, M2, M3


def true_max(p, D, k, w):
    cws = all_codewords(p, D, k); n = len(D)
    if p ** n > 3_000_000: return None
    mx = 0
    for u in itertools.product(range(p), repeat=n):
        L = sum(1 for c in cws if sum(1 for i in range(n) if c[i] != u[i]) <= w)
        if L > mx: mx = L
    return mx


def johnson_cap(n, k, w):
    a = n - w; b = k - 1; den = a * a - n * b
    return Fraction(n * n, den) if den > 0 else None


def f2(x):
    try: return float(x)
    except Exception: return float("nan")


if __name__ == "__main__":
    print("=" * 78)
    print("FAST M3 -- subgroup vs random, exact; ladder lower bounds vs true max")
    print("PZ=M2/M1 and M3/M2 are LOWER bounds on max_u L (Paley-Zygmund ladder).")
    print("=" * 78)
    cases = [(7, 6, 2), (11, 5, 2), (13, 4, 2), (11, 10, 2)]
    for (p, n, k) in cases:
        if (p - 1) % n != 0:
            print(f"(skip p={p} n={n}: {n}∤{p-1})"); continue
        H = smooth_subgroup(p, n)
        random.seed(7)
        R = sorted(random.sample(range(p), n))
        dmin = n - k + 1
        print(f"\np={p} n={n} k={k} rho={k/n:.3f} d_min={dmin}  H={H} R={R}")
        print(f"  half-min-dist boundary (1-rho)/2 in coords ~ w={(dmin-1)//2}")
        for w in range(0, n):
            M1H, M2H, M3H = moments(p, H, k, w)
            M1R, M2R, M3R = moments(p, R, k, w)
            pzH = Fraction(M2H, M1H); m32H = Fraction(M3H, M2H)
            pzR = Fraction(M2R, M1R); m32R = Fraction(M3R, M2R)
            mxH = true_max(p, H, k, w); mxR = true_max(p, R, k, w)
            J = johnson_cap(n, k, w)
            jstr = f"{f2(J):.2f}" if J is not None else "PAST-J"
            dM3 = f2(Fraction(M3H - M3R, max(1, M3R)))
            note = ""
            if 2 * w < dmin: note = "[balls disjoint: max=1]"
            print(f"  w={w:2d} d={w/n:.3f} J<={jstr:7}| "
                  f"H:PZ={f2(pzH):.3f} M3/M2={f2(m32H):.3f} max={mxH} | "
                  f"R:PZ={f2(pzR):.3f} max={mxR} | dM3/M3={dM3:+.2e} {note}", flush=True)
    print("\ndone", flush=True)
