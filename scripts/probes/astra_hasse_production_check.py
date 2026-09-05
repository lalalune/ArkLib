#!/usr/bin/env python3
"""A bounded production Hasse search, with every total cap T covered exactly.

Negative margins rule out this dimension certificate, not actual interpolants.
"""

from hashlib import sha256
import json
import astra_hasse_order_two_check as local

N, W, A, P = 262144, 131071, 181353, local.P


def profile(m, s1, s2):
    D = m*A
    H = (D-1)//(W-2)
    coefficient_slices = []
    rank_slices = []
    for h in range(H+1):
        coefficient_slices.append(sum(
            max(0, D-W*(h-j-k)-(W-1)*j-(W-2)*k)
            for j in range(min(s1, h)+1)
            for k in range(min(s2, h-j)+1)))
        if s2:
            rank_slices.append(sum(local.block_rank(h, r, m, s1, s2, P)
                                   for r in range(m+h) if r+(W-2)*h < D))
        else:
            rank_slices.append(sum(min(max(0, min(h, r)-max(0, h-s1)+1), m-r)
                                   for r in range(m) if r+(W-1)*h < D))
    excesses = [c-N*r for c, r in zip(coefficient_slices, rank_slices)]
    slope = sum(excesses)
    moment = sum(h*b for h, b in enumerate(excesses))
    first_T = next((T for T in range(H+1)
                    if sum((T+1-h)*b for h, b in enumerate(excesses[:T+1])) > 0), None)
    if first_T is None and slope > 0:
        first_T = max(H, moment//slope)
    return {"m": m, "s1": s1, "s2": s2, "H": H, "slope": slope,
            "moment": moment, "first_T": first_T}, coefficient_slices, rank_slices


def main():
    # Independently compare slice summation with the earlier direct count API.
    for m, s1, s2 in ((1, 0, 1), (8, 4, 2), (12, 5, 3), (24, 12, 6)):
        row, cs, rs = profile(m, s1, s2)
        H = row["H"]
        for T in (0, H//2, H, H+7):
            C = sum((T+1-h)*c for h, c in enumerate(cs) if h <= T)
            R = sum((T+1-h)*r for h, r in enumerate(rs) if h <= T)
            assert C == local.coefficients(m*A, W, T, s1, s2)
            assert R == local.rank_two(m*A, W, T, m, s1, s2)
            if T >= H:
                assert C-N*R == (T+1)*row["slope"]-row["moment"]

    rows = []
    for m in range(1, 25):
        for s1 in range(min(12, m)+1):
            for s2 in range(1, min(6, m)+1):
                row, _, _ = profile(m, s1, s2)
                assert row["slope"] < 0 and row["first_T"] is None
                rows.append(row)
        # These cached blocks will not be reused at other multiplicities.
        local.block_rank.cache_clear()
    assert len(rows) == 1426
    assert max(row["H"] for row in rows) == 33
    assert max(row["slope"] for row in rows) == -242369

    # Existing first-derivative source: the slice representation must recover
    # the previously established total-cap threshold and nullity exactly.
    calibration, _, _ = profile(166, 51, 0)
    assert calibration["first_T"] == 7159
    margin = 7160*calibration["slope"]-calibration["moment"]
    previous = 7159*calibration["slope"]-calibration["moment"]
    assert margin == 228451639 and previous <= 0
    digest = sha256(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    print(json.dumps({"status": "PASS_BOUNDED_PRODUCTION_HASSE_DIMENSION_EXCLUSION",
                      "field_characteristic": P, "n": N, "degree_bound": W,
                      "agreement_target": A, "profiles_checked": len(rows),
                      "multiplicities": [1, 24], "S1_limit": "min(12,m)",
                      "S2_range": "1..min(6,m)", "total_caps": "every integer T>=0",
                      "slice_direct_comparisons": 16,
                      "maximum_slope": max(row["slope"] for row in rows),
                      "profile_digest": digest, "order_one_calibration": calibration,
                      "calibration_margin": margin, "calibration_previous_margin": previous,
                      "actual_interpolant_nonexistence_proved": False,
                      "prize_bound_proved": False}, indent=2))


if __name__ == "__main__":
    main()
