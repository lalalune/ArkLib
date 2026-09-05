#!/usr/bin/env python3
"""Actual nonjoint MCA witnesses from the smooth middle-band triple.

Counts explicit core-plus-one-point witnesses, not all MCA-bad scalars.
The same-core attribution upper bound is proved in the companion note.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "smooth_middle", Path(__file__).with_name("astra_grand_smooth_middle_counterexample.py"))
assert SPEC is not None and SPEC.loader is not None
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

PRIZE_P = 365375409332725729550921208179070755120141565953
PRIZE_G = 303645430271030343624574566109998498685964493478


def parameters(m: int) -> dict[str, int]:
    assert m >= 4
    n, k, t, q = 16 * m, 8 * m, 4 * m - 2, (2 * m) // 3 + 2
    e = 3 * m + 2 - 3 * q
    s0 = (2 * n) // 3
    assert 0 <= e <= m
    assert t + 6 * m + q == s0 >= k
    assert 3 * (s0 + 1) > 2 * n
    assert t + 4 * m == k - 2
    bound = n - t + 2 * e
    assert bound == 18 * m + 6 - 6 * q < n - 1
    second_t = 3 * m - 1
    total_membership = 25 * m + 2 * second_t
    assert total_membership == 31 * m - 2 < 3 * s0
    deficit = 3 * s0 - total_membership
    return {"m": m, "n": n, "k": k, "triple_size": t, "private_size": q,
            "holes": e, "core_agreement": s0, "event_agreement": s0 + 1,
            "same_core_attribution_upper": bound, "strip_budget": n - 1,
            "second_generator_total_core_deficit": deficit,
            "second_generator_one_core_deficit_at_least": (deficit + 2) // 3}


def seed_geometry(p: int, zeta: int) -> tuple[list[list[int]], list[list[int]], int]:
    polys, cofactors = BASE.seed_check(p, zeta)
    fs = [[0], BASE.mul(polys[0], cofactors[0], p),
          [-a % p for a in BASE.mul(polys[1], cofactors[1], p)]]
    values = [[BASE.eval_poly(poly, pow(zeta, e, p), p) for poly in fs] for e in range(16)]
    # This exact seed check, not a genericity assumption, supplies all covered coordinates.
    assert all(len(set(row)) >= 2 for row in values)
    used = set().union(*(set(block) for block in BASE.SEED_LABELS))
    safe = next(e for e in range(16) if e not in used and len(set(values[e])) == 3)
    return polys, cofactors, safe


def parity_row(xs: list[int], p: int) -> list[int]:
    """A dual row annihilating every polynomial of degree < len(xs)-1."""
    weights = []
    for i, x in enumerate(xs):
        denominator = 1
        for j, y in enumerate(xs):
            if j != i:
                denominator = denominator * (x - y) % p
        weights.append(pow(denominator, -1, p))
    # Direct independent check of the Vandermonde annihilation identity.
    powers = [1] * len(xs)
    for _ in range(len(xs) - 1):
        assert sum(w * v for w, v in zip(weights, powers)) % p == 0
        powers = [v * x % p for v, x in zip(powers, xs)]
    return weights


def full_cell(p: int, m: int) -> dict[str, object]:
    BASE.check_prime(p)
    info = parameters(m)
    n, k, t, q, e = (info[key] for key in ("n", "k", "triple_size", "private_size", "holes"))
    omega = BASE.root_of_two_power_order(p, n)
    domain = [pow(omega, j, p) for j in range(n)]
    seed, cofactors, safe = seed_geometry(p, pow(omega, m, p))
    blocks = [set(j for j in range(n) if j % 16 in labels) for labels in BASE.SEED_LABELS]
    holes = set([j for j in range(n) if j % 16 == safe][:e])
    remaining = sorted(set(range(n)) - set.union(*blocks) - holes)
    triple, remaining = set(remaining[:t]), remaining[t:]
    private = [set(remaining[j * q:(j + 1) * q]) for j in range(3)]
    assert len(remaining) == 3 * q
    cores = [triple | blocks[0] | blocks[1] | private[0],
             triple | blocks[0] | blocks[2] | private[1],
             triple | blocks[1] | blocks[2] | private[2]]
    assert all(len(core) == info["core_agreement"] for core in cores)
    vt = BASE.from_roots([domain[j] for j in sorted(triple)], p)
    lifted = [BASE.lift(poly, m) for poly in seed]
    fs = [[0], BASE.mul(vt, BASE.mul(lifted[0], BASE.lift(cofactors[0], m), p), p),
          [-a % p for a in BASE.mul(vt, BASE.mul(lifted[1], BASE.lift(cofactors[1], m), p), p)]]
    assert max(len(f) for f in fs) <= k - 1
    vals = [[BASE.eval_poly(f, x, p) for x in domain] for f in fs]
    u0 = [None] * n
    u1 = [None] * n
    for i, core in enumerate(cores):
        for j in core:
            a, b = vals[i][j], domain[j] * vals[i][j] % p
            assert u0[j] is None or (u0[j], u1[j]) == (a, b)
            u0[j], u1[j] = a, b
    assert {j for j in range(n) if u0[j] is None} == holes

    # Each tuple stores the decoded local pair index and its extra point.
    witnesses: dict[int, tuple[int, int]] = {}
    for j in sorted(set(range(n)) - holes - triple):
        i = next(i for i in range(3) if vals[i][j] != u0[j])
        gamma = -pow(domain[j], -1, p) % p
        assert gamma not in witnesses and j not in cores[i]
        witnesses[gamma] = (i, j)
    covered_count = len(witnesses)
    assert covered_count == n - t - e

    hole_assignments = []
    for j in sorted(holes):
        local = [(vals[i][j], domain[j] * vals[i][j] % p) for i in range(3)]
        assert len(set(local)) == 3
        chosen = None
        for a in range(min(p, 128)):
            for b in range(min(p, 128)):
                if any(b == g1 for _, g1 in local):
                    continue
                gammas = [(g0 - a) * pow((b - g1) % p, -1, p) % p for g0, g1 in local]
                if len(set(gammas)) == 3 and not (set(gammas) & witnesses.keys()):
                    chosen = a, b, gammas
                    break
            if chosen is not None:
                break
        assert chosen is not None, (p, m, j)
        a, b, gammas = chosen
        u0[j], u1[j] = a, b
        for i, gamma in enumerate(gammas):
            witnesses[gamma] = (i, j)
        hole_assignments.append({"index": j, "u0": a, "u1": b, "gammas": gammas})
    assert all(a is not None for a in u0) and all(b is not None for b in u1)
    assert len(witnesses) == info["same_core_attribution_upper"]

    parity_checked = 0
    for gamma, (i, j) in witnesses.items():
        support = cores[i] | {j}
        assert len(support) == info["event_agreement"]
        h = BASE.mul(fs[i], [1, gamma], p)
        assert len(h) <= k
        assert all(BASE.eval_poly(h, domain[a], p) == (u0[a] + gamma * u1[a]) % p
                   for a in support)
        # A code-dual parity row certifies that one received component cannot
        # be a degree-<k polynomial on even this (k+1)-point subset of support.
        short = sorted(cores[i])[:k] + [j]
        assert len(set(short)) == k + 1
        parity = parity_row([domain[a] for a in short], p)
        d0 = sum(weight * u0[a] for weight, a in zip(parity, short)) % p
        d1 = sum(weight * u1[a] for weight, a in zip(parity, short)) % p
        assert d0 or d1, "joint explanation was not excluded"
        assert (d0 + gamma * d1) % p == 0
        parity_checked += 1

    # Direct rank checks of the actual normalized local-triple compatibility window.
    ranks = []
    for degree in (4 * m, 4 * m + 1, 5 * m - 1, 5 * m):
        matrix = BASE.syzygy_matrix(lifted, degree)
        rank, _ = BASE.rank_and_kernel(matrix, p)
        nullity = len(matrix[0]) - rank
        expected = max(0, degree - 4 * m + 1) + max(0, degree - 5 * m + 1)
        assert nullity == expected
        ranks.append({"product_degree": degree, "nullity": nullity})
    return {"p": p, **info, "covered_bad_scalars": covered_count,
            "hole_bad_scalars": 3 * e, "certified_distinct_mca_bad": len(witnesses),
            "no_joint_parity_certificates": parity_checked, "seed_safe_hole_label": safe,
            "hole_assignments": hole_assignments, "compatibility_nullities": ranks,
            "global_mca_count": "not computed"}


def main() -> None:
    cells = [full_cell(p, m) for p, m in
             ((193, 4), (257, 8), (BASE.PROTH_P, 4), (BASE.PROTH_P, 8), (BASE.PROTH_P, 16))]
    production = parameters(2**26)
    # P's primality is the existing PrizeShapePrimeP30.prime_P theorem;
    # this probe rechecks only the exact root, seed, and counting certificates.
    assert pow(PRIZE_G, 2**30, PRIZE_P) == 1
    assert pow(PRIZE_G, 2**29, PRIZE_P) != 1
    _, _, safe = seed_geometry(PRIZE_P, pow(PRIZE_G, 2**26, PRIZE_P))
    bound = production["same_core_attribution_upper"]
    assert PRIZE_P > 3 * bound + 4
    production.update({"prime": PRIZE_P, "root": PRIZE_G, "safe_hole_label": safe,
                       "generic_hole_choice_bound": 3 * bound + 4,
                       "verification": "root, seed and arithmetic only; large construction by proof"})
    print(json.dumps({"scope": "Actual MCA lower witnesses and same-core attribution upper; no global upper",
                      "cells": cells, "production": production}, indent=2))


if __name__ == "__main__":
    main()
