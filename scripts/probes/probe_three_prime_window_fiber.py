#!/usr/bin/env python3
"""Probe: the THREE-PRIME WINDOW-FIBER CLASSIFICATION census (n = 30 exact, n = 60 sampled).

Question: what is the right window-fiber law at three-prime moduli?  The O70
coset form (window-t fiber = disjoint unions of mu_d-cosets, d | n, d > t) is
FALSE at n = 30, t = 1 (O105/O111 witness {5,6,12,18,24,25}).  The O111 theorem
`int_windowed_law` says: window-t vanishing of a Z-weight <=> the weight is a
Z-combination of mu_d-coset indicators with d | n, d > t.  Specializing to 0/1
weights:

    CONJECTURED LAW (the 0/1 window-span law):
      F_n(t) = { S : indicator(S) in Z-span{ mu_d-coset indicators, d|n, d>t } }
    i.e. the fiber is the 0/1 PART of the Z-span -- with the LITERAL d > t cut.

Census at n = 30 (exhaustive, exact Z[x]/Phi_30 meet-in-the-middle over halves
[0,15) x [15,30)):
  (i)   F_30(t) for every t = 1..29 (all subsets with power sums 1..t vanishing);
  (ii)  the coset-union subfamily CU(t) (exact-cover test, shared-memo DFS);
  (iii) independent Z-span membership (exact affine-lattice integer solver, NOT
        via the O111 theorem) on all gap witnesses + random positive/negative
        samples, for both the literal d > t cut and (negative control) d > t+1.

Outputs per t: |F(t)|, |CU(t)|, gap count, smallest gap witnesses.
Determines: the t-thresholds where F = CU, and verifies F = 0/1-part-of-Z-span.

n = 60 (sampled): doubled O105 witnesses {2e, 2e+1 : e in S} land in F_60(t)
with the same window depth; coset-union and Z-span membership tested on each.

Exit 0 iff every assertion passes.
"""

import random
import sys
import time
from collections import defaultdict

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from probe_int_windowed_law import cyclotomic, divisors, reduce_mod_phi

import numpy as np

random.seed(232)


# ---------------------------------------------------------------- utilities

def residue_table(n):
    """x^k mod Phi_n for k in [0, n) as tuples of length deg(Phi_n)."""
    phi = cyclotomic(n)
    deg = len(phi) - 1
    out = []
    for k in range(n):
        v = [0] * (k + 1)
        v[k] = 1
        if len(v) < len(phi):
            v += [0] * (len(phi) - len(v))
        out.append(tuple(reduce_mod_phi(v, phi)))
    return out, deg


def full_contrib(n, red, deg):
    """C[e] = concatenated residues of x^{(j*e) % n} for j = 1..n-1 (len (n-1)*deg)."""
    C = np.zeros((n, (n - 1) * deg), dtype=np.int64)
    for e in range(n):
        for j in range(1, n):
            C[e, (j - 1) * deg:j * deg] = red[(j * e) % n]
    return C


def half_profiles(elems, C):
    """All subsets of `elems`: row i = profile of the subset with bit k of i
    selecting elems[k]."""
    arr = np.zeros((1, C.shape[1]), dtype=np.int64)
    for e in elems:
        arr = np.concatenate([arr, arr + C[e]], axis=0)
    return arr


def coset_mask(n, d, r):
    step = n // d
    m = 0
    for s in range(d):
        m |= 1 << (r + s * step)
    return m


def coset_vec(n, d, r):
    step = n // d
    v = [0] * n
    for s in range(d):
        v[r + s * step] = 1
    return v


def span_matrix(n, t):
    """Columns = mu_d-coset indicators, d | n, d > t."""
    cols = []
    for d in divisors(n):
        if d > t:
            for r in range(n // d):
                cols.append(coset_vec(n, d, r))
    return cols


def int_solvable(cols, b):
    """Is b an integer combination of the given columns?  Exact affine-lattice
    row processing: maintain solution x0 + Z-span(B) of the processed rows."""
    m = len(cols)
    nrows = len(b)
    x0 = [0] * m
    B = [[1 if i == j else 0 for j in range(m)] for i in range(m)]
    for i in range(nrows):
        row = [cols[k][i] for k in range(m)]
        c = [sum(row[k] * v[k] for k in range(m)) for v in B]
        c0 = b[i] - sum(row[k] * x0[k] for k in range(m))
        nz = [k for k in range(len(c)) if c[k] != 0]
        if not nz:
            if c0 != 0:
                return False
            continue
        # unimodular column reduction of c to a single nonzero entry
        while len(nz) > 1:
            p = min(nz, key=lambda k: abs(c[k]))
            for k in nz:
                if k == p:
                    continue
                q = c[k] // c[p]
                if q:
                    c[k] -= q * c[p]
                    B[k] = [B[k][u] - q * B[p][u] for u in range(m)]
            nz = [k for k in range(len(c)) if c[k] != 0]
        p = nz[0]
        g = c[p]
        if c0 % g != 0:
            return False
        tcoef = c0 // g
        x0 = [x0[u] + tcoef * B[p][u] for u in range(m)]
        B.pop(p)
    return True


class CosetUnionTester:
    """Exact-cover feasibility 'S is a disjoint union of mu_d-cosets, d in ds',
    with a memo shared across queries (feasibility depends only on the mask)."""

    def __init__(self, n, ds):
        self.bymin = defaultdict(list)
        for d in ds:
            for r in range(n // d):
                m = coset_mask(n, d, r)
                low = (m & -m).bit_length() - 1
                self.bymin[low].append(m)
        self.memo = {0: True}

    def feasible(self, mask):
        memo = self.memo
        got = memo.get(mask)
        if got is not None:
            return got
        low = (mask & -mask).bit_length() - 1
        res = False
        for cm in self.bymin[low]:
            if cm & mask == cm and self.feasible(mask ^ cm):
                res = True
                break
        memo[mask] = res
        return res


def mask_to_set(mask):
    return [e for e in range(64) if (mask >> e) & 1]


# ---------------------------------------------------------------- n = 30 census

def census_n30():
    n = 30
    red, deg = residue_table(n)
    C = full_contrib(n, red, deg)
    t0 = time.time()
    P1 = half_profiles(range(15), C)
    P2 = half_profiles(range(15, 30), C)

    # MITM on the j = 1 block
    block1 = defaultdict(list)
    for i in range(P2.shape[0]):
        block1[tuple(P2[i, :deg])].append(i)
    members = []  # (ia, ib)
    for ia in range(P1.shape[0]):
        key = tuple(-P1[ia, :deg])
        for ib in block1.get(key, ()):
            members.append((ia, ib))
    print(f"[n=30] |F(1)| = {len(members)}  ({time.time()-t0:.1f}s)")

    # window depth tf per member: largest t with blocks 1..t all zero
    ia_arr = np.array([m[0] for m in members])
    ib_arr = np.array([m[1] for m in members])
    tf = np.empty(len(members), dtype=np.int64)
    for lo in range(0, len(members), 50000):
        hi = min(lo + 50000, len(members))
        prof = P1[ia_arr[lo:hi]] + P2[ib_arr[lo:hi]]
        nzblock = (prof.reshape(hi - lo, n - 1, deg) != 0).any(axis=2)
        first = np.argmax(nzblock, axis=1)  # 0 if all-False too
        allzero = ~nzblock.any(axis=1)
        depth = np.where(allzero, n - 1, first)  # blocks 0..first-1 zero -> tf = first (block i = window i+1)
        tf[lo:hi] = depth
    assert (tf >= 1).all(), "every member vanishes at j=1 by construction"

    # P1 over elems 0..14, P2 over 15..29; bit k of a half index = element
    # (base + k), so the full element mask is ia | (ib << 15).
    masks = [ia | (ib << 15) for ia, ib in members]

    # strata of t: the coset family {d : d | 30, d > t} changes at divisors
    strata = [(1, 1), (2, 2), (3, 4), (5, 5), (6, 9), (10, 14), (15, 29)]
    testers = {rep: CosetUnionTester(n, [d for d in divisors(n) if d > rep])
               for rep, _ in strata}

    t0 = time.time()
    cu_depth = np.zeros(len(members), dtype=np.int64)
    for idx, mask in enumerate(masks):
        depth = 0
        for rep, top in strata:
            if testers[rep].feasible(mask):
                depth = top
            else:
                break
        cu_depth[idx] = depth
    print(f"[n=30] coset-union depths computed ({time.time()-t0:.1f}s)")

    # consistency: CU(t) subset of F(t)  (coset union with d > t must vanish on window t)
    assert (np.minimum(cu_depth, n - 1) <= tf).all(), "CU(t) must be inside F(t)"

    # census table
    print(f"\n[n=30] CENSUS  (F = window fiber, CU = coset unions, gap = F \\ CU)")
    print(f"{'t':>3} {'|F(t)|':>8} {'|CU(t)|':>8} {'gap':>7}  divisors d>t")
    gap_by_t = {}
    for t in range(1, n):
        ft = int((tf >= t).sum())
        cu = int(((tf >= t) & (cu_depth >= t)).sum())
        gap = ft - cu
        gap_by_t[t] = gap
        ds = [d for d in divisors(n) if d > t]
        print(f"{t:>3} {ft:>8} {cu:>8} {gap:>7}  {ds}")

    # smallest gap witnesses per t with gap > 0
    print("\n[n=30] smallest gap witnesses (F(t) but not CU(t)):")
    witnesses_by_t = {}
    for t in range(1, n):
        if gap_by_t[t] == 0:
            continue
        idxs = [i for i in range(len(members)) if tf[i] >= t > cu_depth[i]]
        idxs.sort(key=lambda i: (bin(masks[i]).count("1"), masks[i]))
        witnesses_by_t[t] = idxs
        shown = [sorted(mask_to_set(masks[i])) for i in idxs[:4]]
        print(f"  t={t}: {len(idxs)} witnesses; smallest: {shown}")

    # O105 witness diagnostics
    o105 = {5, 6, 12, 18, 24, 25}
    o105_mask = sum(1 << e for e in o105)
    i105 = masks.index(o105_mask)
    print(f"\n[n=30] O105 witness {sorted(o105)}: window depth tf = {tf[i105]}, "
          f"coset-union depth = {cu_depth[i105]}")
    assert tf[i105] == 1 and cu_depth[i105] == 0

    # ---- independent Z-span verification (exact integer solver, literal d > t)
    print("\n[n=30] independent Z-span checks (literal d > t cut):")
    rng = random.Random(305)
    all_masks_set = set(masks)
    for t in [1, 2, 3, 5, 6, 10, 15]:
        cols = span_matrix(n, t)
        sample = []
        # all gap witnesses (up to 40) at this t
        for i in witnesses_by_t.get(t, [])[:40]:
            sample.append((masks[i], True))
        # random fiber members at depth >= t
        pool = [i for i in range(len(members)) if tf[i] >= t]
        for i in rng.sample(pool, min(30, len(pool))):
            sample.append((masks[i], True))
        # random NON-members of F(t): random masks outside F(1) (hence outside
        # F(t), and the span law predicts non-membership in the d>t span)
        neg = 0
        while neg < 30:
            m = rng.getrandbits(n)
            if m in all_masks_set:
                continue
            sample.append((m, False))
            neg += 1
        # members of F(1) that are NOT in F(t) (for t > 1): sharp negatives
        if t > 1:
            sharp = [i for i in range(len(members)) if tf[i] < t]
            for i in rng.sample(sharp, min(20, len(sharp))):
                sample.append((masks[i], False))
        bad = 0
        for m, expect in sample:
            b = [(m >> e) & 1 for e in range(n)]
            got = int_solvable(cols, b)
            if got != expect:
                bad += 1
                print(f"  MISMATCH t={t} S={sorted(mask_to_set(m))} "
                      f"expect={expect} got={got}")
        assert bad == 0, f"Z-span law violated at t={t}"
        print(f"  t={t}: {len(sample)} membership checks "
              f"(span <=> fiber): all agree")

    # negative control on the threshold: gap witnesses at t must NOT be in the
    # d > t' span for the first t' > t where the divisor set shrinks
    print("\n[n=30] threshold sharpness (witness in d>t span, not d>t' span):")
    for t in sorted(witnesses_by_t):
        i = witnesses_by_t[t][0]
        m = masks[i]
        b = [(m >> e) & 1 for e in range(n)]
        tprime = tf[i] + 1  # first failing window
        a = int_solvable(span_matrix(n, t), b)
        c = int_solvable(span_matrix(n, int(tprime)), b)
        assert a and not c
        print(f"  t={t}: witness {sorted(mask_to_set(m))}: in span(d>{t}) = {a}, "
              f"in span(d>{tprime}) = {c}  (tf = {tf[i]})")

    return masks, tf, cu_depth, witnesses_by_t


# ---------------------------------------------------------------- n = 60 sampled

def sampled_n60(masks30, tf30, witnesses_by_t):
    n = 60
    red, deg = residue_table(n)
    print(f"\n[n=60] sampled checks (deg Phi_60 = {deg})")

    def window_depth(S):
        t = 0
        for j in range(1, n):
            acc = [0] * deg
            for e in S:
                r = red[(j * e) % n]
                acc = [a + b for a, b in zip(acc, r)]
            if any(acc):
                return t
            t = j
        return n - 1

    strata = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 9), (10, 11), (12, 14),
              (15, 19), (20, 29), (30, 59)]
    testers = {rep: CosetUnionTester(n, [d for d in divisors(n) if d > rep])
               for rep, _ in strata}

    def cu_depth(S):
        mask = sum(1 << e for e in S)
        depth = 0
        for rep, top in strata:
            if testers[rep].feasible(mask):
                depth = top
            else:
                break
        return depth

    # doubled O105-type witnesses: S2 = {2e, 2e+1 : e in S}
    rng = random.Random(607)
    checked = 0
    gap_found = 0
    for t, idxs in sorted(witnesses_by_t.items()):
        for i in idxs[:6]:
            S = mask_to_set(masks30[i])
            S2 = sorted([2 * e for e in S] + [2 * e + 1 for e in S])
            wd = window_depth(S2)
            cd = cu_depth(S2)
            assert wd >= tf30[i], "doubling must preserve window depth"
            ok_span = int_solvable(span_matrix(n, t), [1 if e in S2 else 0
                                                       for e in range(n)])
            assert ok_span, "doubled witness must lie in the d>t span at n=60"
            checked += 1
            if cd < t:
                gap_found += 1
            print(f"  doubled witness (t={t}) {S2}: window depth {wd}, "
                  f"coset-union depth {cd}, in span(d>{t}) = {ok_span}"
                  + ("  [GAP at n=60]" if cd < t else ""))
    assert checked > 0 and gap_found > 0, "expected n=60 gap witnesses"

    # random Z-span elements with 0/1 values: verify they vanish + tally CU
    print("  random 0/1 span elements:")
    for t in [1, 2, 3, 5]:
        cols = span_matrix(n, t)
        found = 0
        gaps = 0
        tries = 0
        while found < 25 and tries < 200000:
            tries += 1
            k = rng.randint(2, 4)
            picks = rng.sample(range(len(cols)), k)
            coefs = [rng.choice([-1, 1, 1]) for _ in picks]
            w = [sum(c * cols[p][e] for c, p in zip(coefs, picks))
                 for e in range(n)]
            if not all(x in (0, 1) for x in w):
                continue
            if sum(w) == 0:
                continue
            S = [e for e in range(n) if w[e]]
            wd = window_depth(S)
            assert wd >= t, f"span element must vanish on window {t}: {S}"
            found += 1
            if cu_depth(S) < t:
                gaps += 1
        print(f"  t={t}: {found} sampled 0/1 span elements, all vanish on "
              f"window {t}; {gaps} are NOT coset unions (gap examples)")


def main():
    masks30, tf30, cud30, wits = census_n30()
    sampled_n60(masks30, tf30, wits)
    print("\nPROBE PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
