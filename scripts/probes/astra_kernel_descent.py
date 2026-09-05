#!/usr/bin/env python3
"""Exact checks for same-kernel repair/descent, not a protocol certificate.

See docs/kb/astra_kernel_descent_2026-09-04.md for the general proof and the
distinction between a full source kernel and a projected subspace.
"""
from __future__ import annotations

import json
from math import comb

from astra_colon_audit import matrix_rank
from astra_companion_parameters import N, W, locator_rank
from astra_companion_shared_candidate import coefficients_fast

UPSTREAM = "032154395c51fd6f77715a7f42d9a987ab9fb48a"


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss elimination with exact divisions."""
    a = [row[:] for row in matrix]
    previous, sign = 1, 1
    for k in range(len(a)-1):
        pivot = next((j for j in range(k, len(a)) if a[j][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign *= -1
        diagonal = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = a[i][j]*diagonal-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator//previous
        for i in range(k+1, len(a)):
            a[i][k] = 0
        previous = diagonal
    return sign*a[-1][-1]


def binomial_determinant_checks() -> int:
    checks = 0
    for degree in range(48):
        for slope in range(min(degree, 10)+1):
            matrix = [[comb(degree-j, b) for j in range(slope+1)]
                      for b in range(slope+1)]
            assert determinant(matrix) == (-1)**(slope*(slope+1)//2)
            checks += 1
    return checks


def local_matrix_checks() -> int:
    """Check small instances of order>YS+R => divisibility by t.

    Substitute A=v+Rt directly. Append extraction rows for every t^0
    coefficient. Unchanged rank means all contact-kernel vectors have t^0=0.
    These finite tests check transcription, not the general mathematical proof.
    """
    checks = 0
    for prime in (2, 5):
        for ys in range(5):
            for slope in range(min(ys, 2)+1):
                order = ys+slope+1
                basis = [(x,h,j) for x in range(order)
                         for j in range(slope+1) for h in range(ys-j+1)]
                rows = {}
                for column,(x,h,j) in enumerate(basis):
                    for b in range(h+1):
                        t, r = x+h-b, j+h-b
                        if t+2*b < order:
                            row = rows.setdefault((t,b,r), [0]*len(basis))
                            row[column] = comb(h,b) % prime
                matrix = list(rows.values())
                rank = matrix_rank(matrix, prime)
                extraction = [[int(k == column) for k in range(len(basis))]
                              for column,(x,_,_) in enumerate(basis) if x == 0]
                assert matrix_rank(matrix+extraction, prime) == rank
                checks += 1
    return checks


def rfree_local_rank(order: int, total: int) -> int:
    """Codomain dimension for ordinary (t,A)-jets with Z degree<=total-Aexp."""
    assert order >= 0 and total >= 0
    return sum((order-b)*(total+1-b) for b in range(min(order, total+1)))


def rfree_coefficients(weight: int, total: int) -> int:
    """R-free polynomials of contact weight<=weight and residual total<=total."""
    return sum((total+1-h)*(weight+1-W*h)
               for h in range(min(total, weight//W)+1))


def main() -> None:
    ys, slope, total = 47, 10, 2364
    contact_lower = W*ys-slope
    max_order = ys+slope
    required_order_sum = contact_lower+1
    minimum_positive_nodes = (required_order_sum+max_order-1)//max_order
    coefficients = rfree_coefficients(contact_lower, total)
    assert coefficients == coefficients_fast(contact_lower+1, total, 0)
    assert coefficients == 347392733438
    for order in range(max_order+1):
        rho = rfree_local_rank(order, total)
        assert rho == locator_rank(order, total, 0)
        assert rho == order*(order+1)*(total+1)//2-order*(order-1)*(order+1)//6
    rho33, rho34, rho57 = [rfree_local_rank(b,total) for b in (33,34,57)]
    deficit = coefficients-N*rho33
    minimum_high_nodes = (deficit+rho57-rho33-1)//(rho57-rho33)
    assert (contact_lower, max_order, minimum_positive_nodes) == (6160327,57,108076)
    assert (rho33,rho57,deficit,minimum_high_nodes) == (1320781,3878489,1157918974,453)
    # Tight rounded consequences of these particular coarse profile inequalities.
    assert (minimum_positive_nodes-1)*max_order < required_order_sum <= minimum_positive_nodes*max_order
    assert N*rho33+(minimum_high_nodes-1)*(rho57-rho33) < coefficients
    assert coefficients <= N*rho33+minimum_high_nodes*(rho57-rho33)
    # A profile passing both necessary tests is not a constructed polynomial.
    assert N*34 > contact_lower and N*rho34 >= coefficients
    print(json.dumps({
        "status": "VALID_SAME_KERNEL_CRITERION_NO_PROTOCOL_OR_BINDING_EXCLUSION",
        "upstream": UPSTREAM,
        "factor_exact_degrees_total_YS_R": [total,ys,slope],
        "contact_degree_lower_bound": contact_lower,
        "local_order_upper_if_irreducible_positive_R": max_order,
        "necessary_order_sum_at_least": required_order_sum,
        "necessary_positive_order_nodes_at_least": minimum_positive_nodes,
        "rfree_repair_coefficient_count": coefficients,
        "rfree_rank_at_order33": rho33,
        "rfree_rank_at_order57": rho57,
        "uniform_order33_repair_nullity_lower": deficit,
        "necessary_order_at_least34_nodes": minimum_high_nodes,
        "arithmetic_profile_not_excluded": {"order":34,"nodes":N,
            "order_sum":N*34,"rfree_rank_upper":N*rho34,
            "warning":"No polynomial, universal factor, or far/large-family witness asserted"},
        "binomial_determinant_checks": binomial_determinant_checks(),
        "direct_local_matrix_checks": local_matrix_checks(),
        "scope": "Full nonzero contact kernel; projected-subspace stability is a separate obligation"
    },indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
