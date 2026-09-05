#!/usr/bin/env python3
"""Finite checks for the secant/profile note; no prize or score certificate."""

from fractions import Fraction
from math import comb


def main():
    n, a, w, e, y = 262144, 181353, 131071, 80791, 47
    nu = 34
    c_min, c_example = w*y-10, w*y
    total = 2364
    for c in (c_min, c_example):
        repair9 = sum((total+1-j)*max(0,c+1-w*j+r)
                      for j in range((c+9)//w+1)
                      for r in range(min(j,9)+1))
        repair0 = sum((total+1-j)*(c+1-w*j) for j in range(c//w+1))
        rho0 = nu*(nu+1)*(total+1)//2-nu*(nu-1)*(nu+1)//6
        assert n*nu > c
        assert repair9 <= n*11059805 and repair0 <= n*rho0
        assert (nu-1)*a <= c-(w-1)
        assert all(n*min(h,nu) > h*(w-1) for h in range(1,11))

        # These are only aggregate integer degree profiles; no incidence
        # matrix, selected family, or universal factor is being constructed.
        for multiple in (1, 1024, 2**32):
            size, per_node = n*multiple, a*multiple
            pair_sum = nu*n*comb(per_node,2)
            pair_rhs = c*size*(size-1)+(nu*n-c)*size*y*e
            assert 2*pair_sum <= pair_rhs
            triple_sum = n*comb(per_node,3)
            assert 3*triple_sum <= (3*w*comb(size,3)
                +(n-w)*(e-1)*comb(size,2))

    # Sharp examples for the elementary line-count step alone:
    # G=R+product_{j=0}^{d-1}(Y-jZ) is irreducible and regular at the origin.
    # A tangent line with Z-direction1 has R-direction0 and is contained
    # exactly when its Y-direction b is one of 0,...,d-1.
    prime = 101
    for d in range(2,11):
        directions = []
        for b in range(prime):
            value = 1
            for j in range(d):
                value = value*(b-j) % prime
            if value == 0:
                directions.append(b)
        assert directions == list(range(d))

    pair_limit = Fraction(nu*a*a,n)
    triple_limit = Fraction(a**3,n*n)
    assert pair_limit < c_min and triple_limit < w
    print(f"actual_contact_weights_checked: {[c_min,c_example]}")
    print(f"weighted_pair_limit: {pair_limit} < {c_min}")
    print(f"ordinary_triple_limit: {triple_limit} < {w}")
    print(f"contained_secant_neighbor_bound: {y*e}")
    print("sharp_line_count_examples: 9; aggregate_profiles_checked: 6")
    print("PASS: secant inequalities and existing profile tests remain consistent; no C2 gain")


if __name__ == "__main__":
    main()
