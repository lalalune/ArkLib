#!/usr/bin/env python3
"""Checks for the sharp channelwise contact theorem and fixed quotient bound.

See docs/kb/astra_kernel_channel_hermite-2026-09-05.md.
No parameter search or protocol claim.
"""
import json
from collections import Counter
from math import comb

from astra_colon_audit import direct_contact_matrix, matrix_rank, upper_direct


def channel_upper(D, T, Y, S, orders, w):
    return sum(
        (T+1-h-j) * max(0, D-w*h-(w-1)*j-
            sum(count*max(0, m-h-min(h, S-j)) for m, count in orders.items()))
        for h in range(min(T, Y)+1)
        for j in range(min(S, Y-h, T-h)+1)
    )


def sharp_local(h, S, j, m, p):
    """Expand t^a R^j A^(h-k)(A-Rt)^k, then A=v+Rt."""
    k = min(h, S-j)
    a = max(0, m-h-k)
    original = {
        (a+l, h-l, j+l): comb(k, l)*(-1)**l % p
        for l in range(k+1)
        if comb(k, l) % p
    }
    localized = {}
    for (et, ey, er), coefficient in original.items():
        for ev in range(ey+1):
            exponent = et+ey-ev, ev, er+ey-ev
            localized[exponent] = (
                localized.get(exponent, 0)+coefficient*comb(ey, ev)) % p
    order = min(et+2*ev for (et, ev, er), coefficient in localized.items() if coefficient)
    assert order == a+h+k >= m
    assert original[(a, h, j)] == 1
    assert max(er for et, ey, er in original) <= S


def main():
    matrices = 0
    for prime in (2, 5, 101):
        for D,T,Y,S,prescriptions in (
            (6,2,2,1,((2,2),(3,1))),
            (9,4,3,2,((4,4),(4,2))),
            (12,5,4,2,((5,5),(5,3))),
        ):
            for orders in prescriptions:
                histogram = Counter(orders)
                bound = channel_upper(D,T,Y,S,histogram,2)
                old = upper_direct(D,T,Y,S,histogram,2)
                columns, matrix = direct_contact_matrix(
                    prime,D,T,Y,S,(0,1),orders,(1,2),(2,1),2)
                nullity = columns-matrix_rank(matrix,prime)
                assert nullity <= bound <= old
                matrices += 1
        for h,S,j,m in ((4,2,0,6),(4,2,2,6),(1,3,0,5),(0,2,1,3)):
            sharp_local(h,S,j,m,prime)

    rows = []
    for retained, expected_old, expected_new in (
        (166,110165530464248,20556664632356),
        (132,161783400912266,79928722931834),
    ):
        parameters = (23944271,4795,182,41,{retained:262144},131071)
        old, new = upper_direct(*parameters), channel_upper(*parameters)
        assert (old,new) == (expected_old,expected_new)
        assert new > 228451639
        rows.append({"retained_order":retained,"old_upper":old,"new_upper":new,
                     "source_nullity_lower":228451639,"new_minus_source":new-228451639})
    print(json.dumps({"status":"PASS_CHANNEL_HERMITE_NO_BINDING_EXCLUSION",
                     "direct_contact_matrix_checks":matrices,
                     "sharp_local_checks":12,"fixed_quotient_rows":rows},indent=2))


if __name__ == "__main__":
    main()
