#!/usr/bin/env python3
"""Exact arithmetic for the graded-Hermite quotient-kernel upper bound.

The mathematical lemma and existing colon interfaces are documented in
docs/kb/astra_colon_2026-09-04.md. This is not a protocol certificate.
All production rows assume contact order ZERO for F at every node, a favorable
additional hypothesis that is not implied by the factor's degree flag.
"""
from __future__ import annotations

import json
from math import comb

from astra_companion_joint_audit import dense_sources
from astra_companion_limit_audit import EXTRA_SOURCES
from astra_companion_parameters import N, W, locator_rank
from astra_companion_shared_candidate import coefficients_fast

AGREEMENTS = 181353
FLAG = (2364, 47, 10)  # total, YS, R
UPSTREAM = "032154395c51fd6f77715a7f42d9a987ab9fb48a"


def upper_bound(d: int, total: int, ys: int, slope: int,
                orders: dict[int, int], w: int = W) -> int:
    """orders maps prescribed local contact order to number of distinct nodes."""
    assert w >= 2 and min(d, total, ys, slope) >= 0
    assert all(order >= 0 and count >= 0 for order, count in orders.items())
    result = 0
    for i in range(min(total, ys)+1):
        hermite = sum(count*max(0, order-2*i) for order, count in orders.items())
        a, b = d-w*i-hermite, total+1-i
        if a <= 0:
            continue  # Later Y slices can survive when the contact order drops.
        last = min(slope, ys-i, total-i, (a-1)//(w-1))
        sum1, sum2 = last*(last+1)//2, last*(last+1)*(2*last+1)//6
        result += (last+1)*a*b-(a+b*(w-1))*sum1+(w-1)*sum2
    return result


def upper_direct(d, total, ys, slope, orders, w):
    return sum((total+1-i-j)*max(0, d-w*i-(w-1)*j-
                   sum(count*max(0, order-2*i) for order,count in orders.items()))
               for i in range(min(total, ys)+1)
               for j in range(min(slope, total-i, ys-i)+1))


def matrix_rank(rows: list[list[int]], prime: int) -> int:
    if not rows:
        return 0
    a = [[x % prime for x in row] for row in rows]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inverse = pow(a[rank][col], -1, prime)
        a[rank] = [x*inverse % prime for x in a[rank]]
        for j in range(rank+1, len(a)):
            factor = a[j][col]
            if factor:
                a[j] = [(x-factor*y) % prime for x,y in zip(a[j], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def direct_contact_matrix(prime, d, total, ys, slope, nodes, orders, u0, u1, w):
    """Independent monomial substitution: X=x+t, Y=u0+u1 Z+Rt+v.

    Rows are the coefficients of t^a v^b R^c Z^e with a+2b<order.
    This small-field check verifies transcription only, not a production bound.
    """
    basis = [(x,i,j,z) for i in range(min(total, ys)+1)
             for j in range(min(slope, total-i, ys-i)+1)
             for z in range(total-i-j+1)
             for x in range(max(0, d-w*i-(w-1)*j))]
    rows = {}
    for column,(x,i,j,z) in enumerate(basis):
        for node,(point,order) in enumerate(zip(nodes,orders)):
            for a in range(min(x, order-1)+1):
                cx = comb(x,a)*pow(point,x-a,prime)
                for b in range(i+1):  # power of Rt
                    for c in range(i-b+1):  # power of v
                        if a+b+2*c >= order:
                            continue
                        for e in range(i-b-c+1):  # power of u1*Z
                            rest = i-b-c-e
                            value = (cx*comb(i,b)*comb(i-b,c)*comb(i-b-c,e)
                                     *pow(u0[node],rest,prime)*pow(u1[node],e,prime)) % prime
                            if value:
                                key = node,a+b,c,j+b,z+e
                                row = rows.setdefault(key,[0]*len(basis))
                                row[column] = (row[column]+value) % prime
    return len(basis), list(rows.values())


def transcription_checks():
    checks = 0
    for prime in (2, 5, 7):
        for prescribed in ((2,2),(3,1),(1,3),(0,2)):
            for values in (((0,0),(0,0)),((1,2),(2,1))):
                d,total,ys,slope,w = 6,2,2,1,2
                orders = {order: prescribed.count(order) for order in set(prescribed)}
                upper = upper_bound(d,total,ys,slope,orders,w)
                assert upper == upper_direct(d,total,ys,slope,orders,w)
                columns,matrix = direct_contact_matrix(prime,d,total,ys,slope,
                    (0,1),prescribed,values[0],values[1],w)
                nullity = columns-matrix_rank(matrix,prime)
                assert nullity <= upper
                checks += 1
    return checks


def source_row(m,limit,slope):
    d = m*AGREEMENTS
    y = (d-1)//W
    assert d+slope <= W*(y+1)  # The weighted/slope box implies joint YR cap y.
    nullity = coefficients_fast(d,limit,slope)-N*locator_rank(m,limit,slope)
    assert nullity > 0
    t_f,y_f,r_f = FLAG
    c_f = W*y_f-r_f
    reduced = d-c_f,limit-t_f,y-y_f,slope-r_f
    assert min(reduced) >= 0
    bound = upper_bound(*reduced,{m:N})
    return {"source": (m,limit,slope), "original_nullity_lower_bound": nullity,
            "quotient_box_D_T_YS_S": reduced, "all_node_order_zero_assumed": True,
            "factor_contact_degree_lower_bound_used": c_f,
            "quotient_kernel_upper_bound": bound,
            "upper_minus_nullity_lower": bound-nullity,
            "excludes_universal_factor": bound < nullity}


def main():
    sources = [(99,217071,30),(166,7159,51),(270,130000,81)]+dense_sources()+EXTRA_SOURCES
    rows = [source_row(*source) for source in sources]
    assert len(rows) == 52 and not any(row["excludes_universal_factor"] for row in rows)
    t_row = rows[1]
    assert t_row["original_nullity_lower_bound"] == 228451639
    assert t_row["quotient_box_D_T_YS_S"] == (23944271,4795,182,41)
    assert t_row["quotient_kernel_upper_bound"] == 110165530464248
    # At zero received words, Y^m f(X,Z) gives a genuine quotient-contact
    # subspace. This does not make any chosen F universal, nor satisfy a far
    # or large-family hypothesis; it isolates the missing provenance input.
    d,total,ys,slope = t_row["quotient_box_D_T_YS_S"]
    m = 166
    assert m <= min(total,ys) and d > W*m
    x_width, z_width = d-W*m,total-m+1
    subspace = x_width*z_width
    assert subspace == 10123425550
    assert subspace > t_row["original_nullity_lower_bound"]
    # In contrast, the small total-degree-one quotient would be zero if all
    # node orders were retained. This does not assume that for arbitrary F.
    low_quotient = upper_bound(30104598,1,229,51,{166:N})
    assert low_quotient == 0
    result = {"status": "COLON_HERMITE_LEMMA_AND_FAILED_PROVENANCE_TEST_NO_PROTOCOL_PROOF",
              "upstream": UPSTREAM, "factor_flag": FLAG,
              "tiny_matrix_transcription_checks": transcription_checks(),
              "binding_T_row": t_row, "all_given_source_checks": rows,
              "given_sources_excluded": 0,
              "small_k1_quotient_upper_if_all_orders_retained": low_quotient,
              "zero_word_quotient_subspace": {"basis": "Y^166 X^x Z^z",
                  "x_range": (0,x_width-1), "z_range": (0,z_width-1),
                  "dimension": subspace,
                  "warning": "No universal-divisor or far/large-family provenance asserted"}}
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
