#!/usr/bin/env python3
"""probe_kkh26_fold_transport.py — R2/K1 (#357): is the KKH26 bad line fold-covariant?

Hypothesis K1 (ledger) conjectured the KKH26 bad line is NOT fold-invariant (one fold
step strictly shrinks the bad family, improving the ceiling down the tower).

Algebraic observation tested here: for EVEN m, the KKH26 stack

    u0 = x^{rm} / (x^m - w),   u1 = 1 / (x^m - w)     on H (|H| = n)

is FIBER-EVEN (both components are functions of x^2), so the FRI fold
    Fold_beta(f)(x^2) = (f(x)+f(-x))/2 + beta*(f(x)-f(-x))/(2x)
acts on it *independently of beta* and sends it to the SAME construction with
(n, m) -> (n/2, m/2) and the same w:  u0' = y^{r m/2}/(y^{m/2} - w) on H^2.
If the exact bad-gamma sets coincide level-by-level at matched relative radius,
fold-covariance is EXACT and K1's strict-shrink is REFUTED for even m; the
construction is then self-similar down the tower until m = 1, where fiber-evenness
fails and the fold genuinely mixes (beta-dependence appears) — measured last.

Chain (p = 17, full multiplicative group, r = 3, w a non-residue):
    A: n=16, m=4, line code deg <= 4   (u0 = x^12/(x^4-w))
    B: n= 8, m=2, line code deg <= 2
    C: n= 4, m=1, line code deg <= 1
    D: n= 2 (terminal fold of C, per beta), line code deg <= 0

At each level: the EXACT bad-gamma set of the stack (all gamma in F_p, all witness
sets S with |S| >= (1-delta)*n), per the in-tree mcaEvent clauses (line membership +
no-joint-pair). delta in {1/4, 3/8, 1/2} reported.

Exit 0 iff all structural assertions (fiber-evenness, fold = next level, set
equalities asserted only where found) pass.
"""

import sys
from itertools import combinations

P = 17
R = 3
W = 3  # non-residue mod 17 (3 is primitive)


def inv(a):
    return pow(a % P, P - 2, P)


def subgroup(order):
    g = 3  # primitive root mod 17
    h = pow(g, (P - 1) // order, P)
    return sorted(pow(h, i, P) for i in range(order))


def extendable(points, vals, deg):
    """Exists poly of degree <= deg through (points[i], vals[i])? Gaussian rank test."""
    rows = [[pow(x, j, P) for j in range(deg + 1)] + [v % P]
            for x, v in zip(points, vals)]
    m_, ncols = len(rows), deg + 2
    r = 0
    for c in range(ncols - 1):
        piv = next((i for i in range(r, m_) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        rinv = inv(rows[r][c])
        rows[r] = [a * rinv % P for a in rows[r]]
        for i in range(m_):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == m_:
            break
    # inconsistent iff some row is (0,...,0 | nonzero)
    for i in range(m_):
        if all(a == 0 for a in rows[i][:-1]) and rows[i][-1]:
            return False
    return True


def stack(H, m):
    u0 = {x: pow(x, R * m, P) * inv(pow(x, m, P) - W) % P for x in H}
    u1 = {x: inv(pow(x, m, P) - W) for x in H}
    return u0, u1


def lagrange_vals(pts, vals, xs):
    """Values on xs of the unique poly of deg <= len(pts)-1 through (pts, vals)."""
    out = []
    for x in xs:
        acc = 0
        for i, (xi, vi) in enumerate(zip(pts, vals)):
            num, den = 1, 1
            for j, xj in enumerate(pts):
                if j == i:
                    continue
                num = num * (x - xj) % P
                den = den * (xi - xj) % P
            acc = (acc + vi * num * inv(den)) % P
        out.append(acc)
    return tuple(out)


def bad_gammas(H, u0, u1, deg, min_size):
    """Exact mcaEvent bad-gamma set.

    Soundness of the reduction: a witness S sits inside the agreement set A of the
    line with some codeword; the joint clause is ANTITONE in S (joint pairs restrict
    to subsets), so if S != A is a witness then A is too. Hence: bad gamma iff some
    agreeing codeword has |A| >= min_size and the joint test fails on the FULL A.
    Codewords with |A| >= min_size >= deg+1 are found by interpolation through
    (deg+1)-subsets of positions."""
    n = len(H)
    bad = set()
    pos_subsets = list(combinations(range(n), deg + 1))
    for gamma in range(P):
        line = [(u0[x] + gamma * u1[x]) % P for x in H]
        cands = set()
        for T in pos_subsets:
            pts = [H[i] for i in T]
            vals = [line[i] for i in T]
            cands.add(lagrange_vals(pts, vals, H))
        found = False
        for cw in cands:
            A = [i for i in range(n) if cw[i] == line[i]]
            if len(A) < min_size:
                continue
            Apts = [H[i] for i in A]
            if extendable(Apts, [u0[H[i]] for i in A], deg) and \
               extendable(Apts, [u1[H[i]] for i in A], deg):
                continue
            bad.add(gamma)
            found = True
            break
        if found:
            continue
    return bad


def fold(H, f, beta):
    """FRI fold onto H^2 (assumes -x in H for x in H)."""
    inv2 = inv(2)
    out = {}
    for x in H:
        y = pow(x, 2, P)
        if y in out:
            continue
        ev = (f[x] + f[(-x) % P]) * inv2 % P
        od = (f[x] - f[(-x) % P]) * inv2 % P * inv(x) % P
        out[y] = (ev + beta * od) % P
    return out


def main():
    chain = [(16, 4, 4), (8, 2, 2), (4, 1, 1)]
    deltas = [(0.25, "1/4"), (0.375, "3/8"), (0.5, "1/2")]
    stacks = {}
    print(f"p={P}, r={R}, w={W} (non-residue); chain (n,m,deg): {chain}")

    # build stacks and assert fiber-evenness + fold self-similarity at even m
    for (n, m, dq) in chain:
        H = subgroup(n)
        stacks[n] = (H, *stack(H, m))
    for (n, m, dq) in chain[:-1]:
        H, u0, u1 = stacks[n]
        # fiber-evenness: f(x) = f(-x)
        for f in (u0, u1):
            for x in H:
                assert f[x] == f[(-x) % P], "fiber-evenness FAILS (unexpected)"
        # fold equals next level, for every beta
        Hn, v0, v1 = stacks[n // 2]
        for beta in range(P):
            f0 = fold(H, u0, beta)
            f1 = fold(H, u1, beta)
            assert f0 == v0 and f1 == v1, "fold != next-level stack (unexpected)"
        print(f"  n={n} m={m}: fiber-even OK; Fold_beta(stack) == stack(n/2, m/2) "
              f"for ALL beta — fold-covariance EXACT (beta-independent)")

    # exact bad-gamma sets, matched relative radii
    print("\nexact bad-gamma sets per level (matched relative delta):")
    results = {}
    for (n, m, dq) in chain:
        H, u0, u1 = stacks[n]
        for dval, dname in deltas:
            ms = -(-int((1 - dval) * n + 1e-9) // 1)
            ms = int((1 - dval) * n + 1e-9)
            ms = max(ms, 1)
            bad = bad_gammas(H, u0, u1, dq, ms)
            results[(n, dname)] = bad
            print(f"  n={n:2d} m={m} deg<={dq} delta={dname} (|S|>={ms}): "
                  f"#bad={len(bad)} bad={sorted(bad)}")

    print("\nlevel-to-level comparison (fold preserves the bad set?):")
    for dname in [d for _, d in deltas]:
        chain_sets = [results[(n, dname)] for (n, _, _) in chain]
        rels = []
        for i in range(len(chain_sets) - 1):
            a, b = chain_sets[i], chain_sets[i + 1]
            rel = "EQUAL" if a == b else ("SUBSET" if a < b else
                                          ("SUPERSET" if a > b else "INCOMPARABLE"))
            rels.append(rel)
        print(f"  delta={dname}: A->B {rels[0]}, B->C {rels[1]}")

    # terminal m=1 fold: beta-dependence appears
    print("\nterminal fold (C: n=4, m=1 -> n=2, deg<=0), per beta:")
    H, u0, u1 = stacks[4]
    counts = {}
    for beta in range(P):
        f0 = fold(H, u0, beta)
        f1 = fold(H, u1, beta)
        H2 = sorted(f0.keys())
        bad = bad_gammas(H2, f0, f1, 0, 2)
        counts[beta] = len(bad)
    distinct = sorted(set(counts.values()))
    print(f"  bad-count per beta: {counts}")
    print(f"  distinct counts across beta: {distinct} "
          f"(beta-dependence {'PRESENT' if len(distinct) > 1 else 'ABSENT'})")
    print("\nexit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
