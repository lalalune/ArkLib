#!/usr/bin/env python3
"""Exact MCA error profiles for tiny smooth-domain Reed-Solomon codes.

Computes, by exhaustive enumeration, the EXACT in-tree mcaEvent error

    eps_mca(C, delta) = max_{u0,u1} (1/p) * #{gamma : mcaEvent C delta u0 u1 gamma}

(ArkLib/Data/CodingTheory/ProximityGap/Errors.lean, ABF26 Def 4.3) for a ladder
of tiny RS codes on smooth (multiplicative subgroup) domains, to observe where
the bad-scalar count jumps as the radius crosses the unique-decoding / Johnson /
capacity landmarks.  This is conjecture-discovery instrumentation, not proof:
finite computation can refute candidate delta* formulas, never prove them.

Key reduction (what makes this feasible): the mcaEvent for (u0, u1, gamma)
depends only on the SYNDROMES s0 = H u0, s1 = H u1:
  * "w agrees with some codeword on S" (extendability from S) is invariant
    under shifting w by a codeword, hence a function of the coset/syndrome;
  * the line point u0 + gamma*u1 has syndrome s0 + gamma*s1;
  * pairJointAgreesOn C S u0 u1 splits as ext(u0,S) AND ext(u1,S) (the two
    codeword witnesses are independent), each coset-invariant.
So the sup over p^{2n} word pairs collapses to p^{2(n-k)} syndrome pairs.

Witness discipline: the syndrome-reduced computation is cross-checked against
a naive word-level enumeration on the smallest instance (two independent
computations must agree exactly), and eps_mca is asserted monotone in delta.
Exit 0 iff all assertions pass.
"""

from itertools import product, combinations


# ---------------------------------------------------------------- F_p linear algebra

def rref(mat, p):
    """Row-reduce mat over F_p; returns (rref_rows, pivot_cols)."""
    m = [row[:] for row in mat]
    rows, cols = len(m), len(m[0]) if m else 0
    piv = []
    r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p != 0), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        inv = pow(m[r][c], p - 2, p)
        m[r] = [(x * inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p != 0:
                f = m[i][c]
                m[i] = [(a - f * b) % p for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return m[:r], piv


def nullspace(mat, p):
    """Basis of {v : mat . v = 0} over F_p."""
    red, piv = rref(mat, p)
    cols = len(mat[0])
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * cols
        v[f] = 1
        for r, c in enumerate(piv):
            v[c] = (-red[r][f]) % p
        basis.append(v)
    return basis


def solve_particular(H, s, p):
    """One w with H . w = s (free variables zero)."""
    rows = [H[i] + [s[i]] for i in range(len(H))]
    red, piv = rref(rows, p)
    n = len(H[0])
    w = [0] * n
    for r, c in enumerate(piv):
        if c == n:
            raise ValueError("inconsistent system")
        w[c] = red[r][n]
    return w


# ---------------------------------------------------------------- RS code machinery

def smooth_domain(p, n):
    """Element of order n in F_p^* (needs n | p-1), returning [g^0, ..., g^{n-1}]."""
    assert (p - 1) % n == 0, f"need n | p-1, got n={n}, p={p}"
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element found")


def ext_from(word, S, xs, k, p):
    """Does word|_S extend to a degree-<k polynomial evaluation?  Any <=k points
    always interpolate; beyond k, interpolate the first k points of S and verify
    the rest (Lagrange)."""
    if len(S) <= k:
        return True
    base, rest = S[:k], S[k:]
    for j in rest:
        # Lagrange evaluation at xs[j] of the interpolant through base
        val = 0
        for a in base:
            num, den = 1, 1
            for b in base:
                if b != a:
                    num = num * ((xs[j] - xs[b]) % p) % p
                    den = den * ((xs[a] - xs[b]) % p) % p
            val = (val + word[a] * num * pow(den, p - 2, p)) % p
        if val != word[j] % p:
            return False
    return True


def build_instance(p, n, k):
    """Returns (xs, H, syndromes list, ext bitmask per syndrome, subsets list)."""
    xs = smooth_domain(p, n)
    G = [[pow(x, j, p) for x in xs] for j in range(k)]  # k x n generator
    H = nullspace(G, p)                                  # (n-k) x n parity check
    assert len(H) == n - k
    subsets = []
    for size in range(k + 1, n + 1):                     # only |S| > k can refuse a pair
        subsets.extend(combinations(range(n), size))
    syndromes = list(product(range(p), repeat=n - k))
    ext_mask = {}
    for s in syndromes:
        w = solve_particular(H, list(s), p)
        mask = 0
        for bit, S in enumerate(subsets):
            if ext_from(w, list(S), xs, k, p):
                mask |= 1 << bit
        ext_mask[s] = mask
    return xs, H, syndromes, ext_mask, subsets


def admissible_mask(subsets, m):
    """Bitmask of subsets with |S| >= m (the (1-delta)n size clause)."""
    mask = 0
    for bit, S in enumerate(subsets):
        if len(S) >= m:
            mask |= 1 << bit
    return mask


def eps_profile_syndrome(p, n, k):
    """max bad-gamma count per witness-size threshold m, via syndrome reduction."""
    _, _, syndromes, ext_mask, subsets = build_instance(p, n, k)
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    best = {m: 0 for m in adm}
    nz = [s for s in syndromes if any(s)]
    for s0 in syndromes:
        for s1 in nz:                       # s1 = 0 never produces a bad gamma
            bad_masks = []
            for g in range(p):
                line = tuple((a + g * b) % p for a, b in zip(s0, s1))
                # bad at S: line extends AND NOT (u0 extends AND u1 extends)
                bad_masks.append(ext_mask[line] & ~(ext_mask[s0] & ext_mask[s1]))
            for m, am in adm.items():
                cnt = sum(1 for bm in bad_masks if bm & am)
                if cnt > best[m]:
                    best[m] = cnt
    return best, subsets


def eps_profile_naive(p, n, k):
    """Word-level recomputation (independent witness; smallest instance only)."""
    xs = smooth_domain(p, n)
    words = list(product(range(p), repeat=n))
    subsets = []
    for size in range(k + 1, n + 1):
        subsets.extend(combinations(range(n), size))
    wext = {}
    for w in words:
        mask = 0
        for bit, S in enumerate(subsets):
            if ext_from(list(w), list(S), xs, k, p):
                mask |= 1 << bit
        wext[w] = mask
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    best = {m: 0 for m in adm}
    for u0 in words:
        for u1 in words:
            bad_masks = []
            for g in range(p):
                line = tuple((a + g * b) % p for a, b in zip(u0, u1))
                bad_masks.append(wext[line] & ~(wext[u0] & wext[u1]))
            for m, am in adm.items():
                cnt = sum(1 for bm in bad_masks if bm & am)
                if cnt > best[m]:
                    best[m] = cnt
    return best


def report(p, n, k, best):
    from math import sqrt
    rho = k / n
    print(f"\nRS[F_{p}, n={n}, k={k}]  rate={rho:.3f}  "
          f"UDR={(1 - rho) / 2:.3f}  Johnson={1 - sqrt(rho):.3f}  capacity={1 - rho:.3f}")
    print(f"  {'m':>3} {'delta=1-m/n':>12} {'max bad gamma':>14} {'eps_mca':>10}")
    prev = None
    for m in sorted(best, reverse=True):
        delta = 1 - m / n
        b = best[m]
        print(f"  {m:>3} {delta:>12.3f} {b:>14} {b}/{p}")
        if prev is not None:
            assert b >= prev, "eps_mca must be monotone nondecreasing in delta"
        prev = b


if __name__ == "__main__":
    # two-witness control: syndrome-reduced == naive word-level on the smallest case
    p0, n0, k0 = 5, 4, 2
    red, _ = eps_profile_syndrome(p0, n0, k0)
    naive = eps_profile_naive(p0, n0, k0)
    assert red == naive, f"witness mismatch: {red} vs {naive}"
    print(f"two-witness control: syndrome-reduced == naive word-level "
          f"at RS[F_{p0}, {n0}, {k0}]  [OK]")

    ladder = [(5, 4, 2), (13, 4, 2), (17, 4, 2), (11, 5, 2), (7, 6, 3), (13, 6, 3)]
    for p, n, k in ladder:
        best, _ = eps_profile_syndrome(p, n, k)
        report(p, n, k, best)

    print("\nReading: 'max bad gamma' is the exact worst-case number of bad scalars")
    print("on any affine line (eps_mca = that count / p).  The jump locations,")
    print("compared against the UDR / Johnson / capacity landmarks per code, are")
    print("the empirical shadow of delta* at toy scale.  Drift across p at fixed")
    print("(n,k), and across (n,k) at fixed rate, is the signal worth fitting.")
    print("\nall assertions passed")
