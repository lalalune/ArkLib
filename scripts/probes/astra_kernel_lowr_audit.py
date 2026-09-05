#!/usr/bin/env python3
"""Exact fixed-cap-nine repair arithmetic; no protocol certificate.

The new necessary profile inequality is documented in
docs/kb/astra_kernel_lowr_2026-09-04.md. No source/helper grid is searched.
"""
from __future__ import annotations

import json

from astra_colon_audit import direct_contact_matrix, matrix_rank
from astra_companion_parameters import N, W, locator_rank
from astra_companion_shared_candidate import coefficients_fast


def rectangle(ni: int, nj: int, offset: int, total: int) -> int:
    return sum(max(0,total+1-offset-i-j) for i in range(ni) for j in range(nj))


def local_rank_literal(order: int, total: int, slope: int) -> int:
    """RCN119.localRankBound using literal positive-part coefficient sums."""
    result = 0
    for row in range(order):
        degree, contact = min(row,total), min(row+1,order-row)
        input_count = rectangle(degree+1,slope+1,0,total)
        kernel_lower = rectangle(max(0,degree+1-contact),
                                 max(0,slope+1-contact),contact,total)
        result += max(0,input_count-kernel_lower)
    return result


def coefficient_count_literal(weight: int, total: int, slope: int) -> int:
    return sum(max(0,total+1-i-j)*max(0,weight+1-W*i-(W-1)*j)
               for i in range(min(total,weight//W)+1)
               for j in range(slope+1))


def matrix_transcription_checks() -> int:
    checks = 0
    for prime in (2,5,101):
        for d,total,slope in ((6,3,1),(9,5,2),(5,3,2)):
            for orders in ((2,2),(3,1),(0,3)):
                _,matrix = direct_contact_matrix(prime,d,total,total,slope,
                    (0,1),orders,(1,2),(2,1),2)
                upper = sum(local_rank_literal(b,total,slope) for b in orders)
                assert matrix_rank(matrix,prime) <= upper
                checks += 1
    return checks


def main() -> None:
    total, ys, factor_slope, repair_slope = 2364,47,10,9
    c = W*ys-factor_slope
    assert c+1+repair_slope == W*ys  # The repair's joint YR degree is <=46.
    coefficients = coefficient_count_literal(c,total,repair_slope)
    assert coefficients == coefficients_fast(c+1,total,repair_slope)
    assert coefficients == 2856185117975
    ranks = [local_rank_literal(b,total,repair_slope) for b in range(58)]
    for b,rank in enumerate(ranks):
        assert b+repair_slope <= total+1
        assert rank == locator_rank(b,total,repair_slope)
        if b:
            assert ranks[b-1] <= rank
    deficit = coefficients-N*ranks[33]
    per_high_node = ranks[57]-ranks[33]
    high_nodes = (deficit+per_high_node-1)//per_high_node
    assert (ranks[33],ranks[57],deficit,high_nodes) == (
        10367785,33389585,138332486935,6009)
    assert N*ranks[33]+(high_nodes-1)*per_high_node < coefficients
    assert coefficients <= N*ranks[33]+high_nodes*per_high_node
    assert coefficients-N*ranks[34] == -43076403945
    print(json.dumps({
        "status":"VALID_LOWER_R_REPAIR_PROFILE_CONSTRAINT_NO_BINDING_EXCLUSION",
        "upstream":"032154395c51fd6f77715a7f42d9a987ab9fb48a",
        "factor_exact_degrees_total_YS_R":[total,ys,factor_slope],
        "repair_box_D_total_slope":[c+1,total,repair_slope],
        "coefficient_count":coefficients,
        "node_rank_at_order33":ranks[33],
        "node_rank_at_order57":ranks[57],
        "uniform_order33_nullity_lower":deficit,
        "necessary_order_at_least34_nodes":high_nodes,
        "previous_rfree_high_node_threshold":453,
        "uniform_order34_nullity_lower":coefficients-N*ranks[34],
        "all_node_ranks_0_through57":ranks,
        "direct_small_contact_matrix_checks":matrix_transcription_checks(),
        "scope":"Nonzero full source kernel, universal positive-R irreducible factor; no projected-subspace closure assumed"
    },indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
