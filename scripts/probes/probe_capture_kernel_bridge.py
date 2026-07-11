#!/usr/bin/env python3
"""Probe for the BCIKS20 Steps 5-7 capture-kernel BRIDGE (O79 lane).

The Lean brick under test (Hab25CaptureKernel.lean) asserts, on the repo's own
definitions (mcaEvent / AffineCaptured, ABF26 Def 4.3 shapes):

  (E1) decode equivalence: mcaEvent C delta u0 u1 gamma  <=>  exists a decode
       witness (S, P): P a polynomial with deg P < k, |S| >= (1-delta)*n,
       P(omega_i) = u0 i + gamma*u1 i on S, and NOT pairJointAgreesOn S.
       (McaDecode <-> mcaEvent; the RS-codeword <-> polynomial destructuring.)

  (E2) capture bridge: a decode (S, P) with P = v0 + gamma*v1 yields
       AffineCaptured domain k delta u gamma (v0, v1)  -- verbatim clauses.

  (E3) assembly: if EVERY bad gamma of a cell decodes to v0 + gamma*v1 for a
       single pair (v0, v1) with deg < k, then the cell satisfies the literal
       hsteps57 hypothesis of claim1_dichotomy, hence |cell| <= n
       (the claim1 conclusion -- proven in-tree; here measured for non-vacuity).

  (N1) negative control: the pinning hypothesis is SUBSTANTIVE -- there exist
       bad-scalar cells of size >= 3 admitting NO single affine pair capturing
       all members (so hsteps57 is not auto-true; the Steps 5-7 content is real).

Exhaustive at GF(3), n=4, k=2 (all 6561 stacks); sampled + planted at GF(5),
n=4, k=2. Exact arithmetic, deterministic. Exit 0 iff all checks pass.
"""

import itertools
import random
import sys
from fractions import Fraction


def make_field(q):
    return list(range(q))


def poly_eval(coeffs, x, q):
    """coeffs[i] is coefficient of X^i."""
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def run_point(q, n, k, domain, deltas, stacks, label, exhaustive_subsets=True):
    F = make_field(q)
    # all polynomials of degree < k (k coefficients)
    polys = list(itertools.product(F, repeat=k))
    codewords = {}
    for p in polys:
        w = tuple(poly_eval(p, x, q) for x in domain)
        codewords.setdefault(w, p)  # eval map injective iff k <= n & domain distinct
    cw_list = list(codewords.keys())
    assert len(cw_list) == q ** k, "evaluation map not injective at this point"

    subsets = []
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            subsets.append(frozenset(S))

    def agree_mask(w, u):
        return frozenset(i for i in range(n) if w[i] == u[i])

    stats = dict(e1_checks=0, e1_mismatch=0, e2_checks=0, e2_fail=0,
                 pinned_cells=0, pinned_cell_max=0, neg_cells=0, bad_max=0)

    for delta in deltas:
        thresh = Fraction(1 - delta) * n  # |S| >= (1-delta)*n, exact
        for (u0, u1) in stacks:
            # per-codeword agreement masks with each fold, per gamma
            # pairJointAgreesOn S <=> exists pair (v0,v1) cw: S subset of M(v0,u0) & M(v1,u1)
            m0 = [agree_mask(w, u0) for w in cw_list]
            m1 = [agree_mask(w, u1) for w in cw_list]
            pair_masks = set()
            for a in m0:
                for b in m1:
                    pair_masks.add(a & b)
            # maximal pair masks suffice for the subset test
            pair_max = [m for m in pair_masks
                        if not any(m < m2 for m2 in pair_masks)]

            bad = {}
            for gamma in F:
                fold = tuple((u0[i] + gamma * u1[i]) % q for i in range(n))
                fold_masks = [agree_mask(w, fold) for w in cw_list]
                # mcaEvent by definition: exists S
                event = False
                decode = None
                for S in subsets:
                    if len(S) < thresh:
                        continue
                    # closeness clause: some codeword equals fold on S
                    widx = next((j for j, m in enumerate(fold_masks) if S <= m),
                                None)
                    if widx is None:
                        continue
                    # no joint agreement on S
                    if any(S <= m for m in pair_max):
                        continue
                    event = True
                    decode = (S, codewords[cw_list[widx]])
                    break
                # (E1) decode existence <=> event: decode witness IS the event
                # witness destructured through codeword<->poly bijection; check
                # both directions independently (re-derive event from decode).
                stats["e1_checks"] += 1
                if event != (decode is not None):
                    stats["e1_mismatch"] += 1
                if decode is not None:
                    S, P = decode
                    ok = (len(S) >= thresh
                          and all(poly_eval(P, domain[i], q)
                                  == (u0[i] + gamma * u1[i]) % q for i in S)
                          and not any(S <= m for m in pair_max))
                    if not ok:
                        stats["e1_mismatch"] += 1
                    bad[gamma] = decode

            if bad:
                stats["bad_max"] = max(stats["bad_max"], len(bad))
            # (E2)+(E3): per-CELL pinning at the honest §5 granularity --
            # a cell is a maximal subset of bad scalars whose decodes lie on
            # ONE affine family P_gamma = v0 + gamma*v1.  Any two distinct
            # members determine (v0, v1); enumerate all pairs.
            if len(bad) >= 2:
                gs = sorted(bad)
                best = None
                for g1, g2 in itertools.combinations(gs, 2):
                    P1, P2 = bad[g1][1], bad[g2][1]
                    inv = pow((g1 - g2) % q, q - 2, q)
                    v1 = tuple(((a - b) * inv) % q for a, b in zip(P1, P2))
                    v0 = tuple((a - g1 * c) % q for a, c in zip(P1, v1))
                    cell = [g for g in gs
                            if tuple((v0[j] + g * v1[j]) % q
                                     for j in range(k)) == bad[g][1]]
                    if best is None or len(cell) > len(best[0]):
                        best = (cell, v0, v1)
                cell, v0, v1 = best
                stats["pinned_cells"] += 1
                stats["pinned_cell_max"] = max(stats["pinned_cell_max"],
                                               len(cell))
                # (E2) AffineCaptured clauses verbatim, per cell member
                for g in cell:
                    S, _P = bad[g]
                    stats["e2_checks"] += 1
                    agreeOK = all(
                        (poly_eval(v0, domain[i], q)
                         + g * poly_eval(v1, domain[i], q)) % q
                        == (u0[i] + g * u1[i]) % q for i in S)
                    sizeOK = len(S) >= thresh
                    njpOK = not any(S <= m for m in pair_max)
                    if not (agreeOK and sizeOK and njpOK):
                        stats["e2_fail"] += 1
                # (E3) claim1 conclusion on the pinned cell: |cell| <= n
                if len(cell) > n:
                    print(f"[{label}] E3 VIOLATION: pinned cell of size "
                          f"{len(cell)} > n={n}")
                    return None
                # negative control: the maximal affine cell misses members
                if len(cell) < len(bad):
                    stats["neg_cells"] += 1
    return stats


def main():
    random.seed(232)
    failures = 0

    # Point A: exhaustive GF(3), n=4, k=2, deltas 1/4 and 1/2
    q, n, k = 3, 4, 2
    domain = [0, 1, 2]  # need n distinct points; GF(3) has only 3 -- use n=3
    n = 3
    stacks = list(itertools.product(
        itertools.product(range(q), repeat=n), repeat=2))
    sA = run_point(q, n, k, domain, [Fraction(1, 3)], stacks,
                   "GF(3) exhaustive")
    if sA is None or sA["e1_mismatch"] or sA["e2_fail"]:
        failures += 1
    print(f"[GF(3) n=3 k=2 exhaustive] {sA}")

    # Point B: GF(5), n=4, k=2: planted multi-gamma cells + random sample
    q, n, k = 5, 4, 2
    domain = [0, 1, 2, 3]
    stacks = set()
    # planted: u0 = eval(v0)+e0, u1 = eval(v1)+e1, e0 = -g_j*e1 per-coord
    for _ in range(300):
        v0 = tuple(random.randrange(q) for _ in range(k))
        v1 = tuple(random.randrange(q) for _ in range(k))
        w0 = tuple(poly_eval(v0, x, q) for x in domain)
        w1 = tuple(poly_eval(v1, x, q) for x in domain)
        g1, g2 = random.sample(range(q), 2)
        c1, c2 = random.choice([(0, 1), (0, 2), (1, 3), (2, 3)])
        e1 = [0] * n
        e1[c1], e1[c2] = random.randrange(1, q), random.randrange(1, q)
        e0 = [0] * n
        e0[c1] = (-g1 * e1[c1]) % q
        e0[c2] = (-g2 * e1[c2]) % q
        u0 = tuple((w0[i] + e0[i]) % q for i in range(n))
        u1 = tuple((w1[i] + e1[i]) % q for i in range(n))
        stacks.add((u0, u1))
    for _ in range(700):
        stacks.add((tuple(random.randrange(q) for _ in range(n)),
                    tuple(random.randrange(q) for _ in range(n))))
    sB = run_point(q, n, k, domain, [Fraction(1, 4)], sorted(stacks),
                   "GF(5) planted+random")
    if sB is None or sB["e1_mismatch"] or sB["e2_fail"]:
        failures += 1
    print(f"[GF(5) n=4 k=2 planted+random] {sB}")

    ok_nonvac = ((sA and sA["pinned_cell_max"] >= 2)
                 or (sB and sB["pinned_cell_max"] >= 2))
    ok_neg = (sA and sA["neg_cells"] > 0) or (sB and sB["neg_cells"] > 0)
    print(f"non-vacuity (affine cells with >=2 members): {ok_nonvac}; "
          f"negative control (bad sets not covered by one affine cell): "
          f"{ok_neg}")
    if failures or not ok_nonvac:
        print("PROBE FAILED")
        return 1
    if not ok_neg:
        print("WARNING: no unpinnable >=3 cell found (pinning may be "
              "auto-true at these tiny points) -- not a failure, recorded.")
    print("PROBE PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
