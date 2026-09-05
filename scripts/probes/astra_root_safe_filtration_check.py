#!/usr/bin/env python3
"""Check the leading-S coefficient filtration and its production arithmetic.

This does not exclude actual kernels or prove production surface properness.
The companion C++ probe exhausts the separately stated bounded margin class.
"""
import json

from astra_hasse_order_two_check import coefficients, direct_rank, rank_one
from astra_hasse_rank_profile_check import A, N, P, W, slices


def first_counts(D, w, T, m, rcap):
    if D <= 0 or T < 0:
        return 0, 0
    assert m >= 1
    C = sum((T+1-h)*sum(max(0, D-w*h+j) for j in range(min(rcap, h)+1))
            for h in range(min(T, (D+rcap-1)//w)+1))
    L = sum((T+1-h)*sum(min(max(0, min(h, r)-max(0, h-rcap)+1), m-r)
                          for r in range(m) if r+(w-1)*h < D)
            for h in range(min(T, m+rcap-1)+1))
    return C, L


def small_checks():
    cases = 0
    strict = 0
    for p in (2, 5, 17, P):
        for D, w, T, m, s1, s2 in (
                (9, 2, 2, 3, 1, 1), (15, 3, 3, 4, 2, 1),
                (19, 4, 3, 5, 2, 2), (23, 5, 3, 6, 3, 2)):
            if s2 >= p:
                continue
            C = coefficients(D, w, T, s1, s2)
            parts = [first_counts(D-j*(w-2), w, T-j, m-j, s1)
                     for j in range(s2+1)]
            for j, (c, rank) in enumerate(parts):
                assert c == coefficients(D-j*(w-2), w, T-j, s1, 0)
                assert rank == rank_one(D-j*(w-2), w, T-j, m-j, s1)
            assert C == sum(c for c, rank in parts)
            for node, u0, u1 in ((0, 0, 0), (2, 3, 4)):
                actual = direct_rank(D, w, T, m, s1, s2, p, node, u0, u1, 2)
                first_actual = [direct_rank(D-j*(w-2), w, T-j, m-j, s1, 0,
                                           p, node, u0, u1, 1)
                                for j in range(s2+1)]
                assert first_actual == [rank for c, rank in parts]
                assert actual >= sum(first_actual)
                strict += actual > sum(first_actual)
                cases += 1
    assert cases == 28 and strict > 0
    return {"direct_local_comparisons": cases, "strict_inequalities": strict}


def production_checks():
    cases = (
        (80, 24, 6, 1042, -4922770342480, 5337770),
        (99, 30, 1, 4156, -1545990052948, 525393),
        (166, 51, 1, 42105, 84317578, 9106260),
        (60, 9, 12, 1000, -8641612426271, 19169209),
    )
    rows = []
    for m, s1, s2, T, expected_margin, expected_gap in cases:
        D = m*A-s2*(A-W+2)
        H = min(T, (D-1)//(W-2))
        cs, ranks = slices(D, W, m, s1, s2, H)
        C = sum((T+1-h)*c for h, c in enumerate(cs))
        L = sum((T+1-h)*rank for h, rank in enumerate(ranks))
        parts = [first_counts(D-j*(W-2), W, T-j, m-j, s1)
                 for j in range(s2+1)]
        assert C == sum(c for c, rank in parts)
        gap = L-sum(rank for c, rank in parts)
        assert (C-N*L, gap) == (expected_margin, expected_gap)
        assert gap >= 0
        margins = [c-N*rank for c, rank in parts]
        assert C-N*L == sum(margins)-N*gap
        assert all(D-j*(W-2) <= (m-j)*A for j in range(s2+1))
        if C-N*L > 0:
            assert any(margin > 0 for margin in margins)
        rows.append({"m": m, "S1": s1, "S2": s2, "T": T, "trimmed_D": D,
                     "second_order_margin": C-N*L, "local_rank_gap": gap,
                     "first_order_slice_margins": margins})
    assert rows[2]["first_order_slice_margins"] == [-9878943152949, 12266178891967]
    return rows


def main():
    print(json.dumps({"status": "PASS_ROOT_SAFE_COEFFICIENT_FILTRATION",
                      "small_checks": small_checks(),
                      "production_checks": production_checks(),
                      "actual_kernels_excluded": False,
                      "production_properness_proved": False,
                      "prize_bound_improved": False,
                      "lean_run_performed": False}, indent=2))


if __name__ == "__main__":
    main()
