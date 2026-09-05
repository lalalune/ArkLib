#!/usr/bin/env python3
"""Exact bounded locator identities; no production locator existence claim."""
import json
from math import gcd

from astra_mca_hosted_receipt_check import DEFAULT, G, N, P, verify


def trim(poly):
    poly = [x % P for x in poly]
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add(a, b, scale=1):
    return trim([(a[j] if j < len(a) else 0)+scale*(b[j] if j < len(b) else 0)
                 for j in range(max(len(a), len(b)))])


def mul(a, b):
    result = [0]*(len(a)+len(b)-1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            result[j+k] = (result[j+k]+x*y) % P
    return trim(result)


def scale(a, scalar):
    return trim([scalar*x for x in a])


def evaluate(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = (value*x+coefficient) % P
    return value


def shift(poly, zeta):
    return [a*pow(zeta, j, P) % P for j, a in enumerate(poly)]


def main():
    archive = verify(DEFAULT)
    assert archive['field_certificate_nodes'] == 14
    assert P % 3 == 2 and P % N == 1 and P > N
    n, degree = 16, 2
    omega = pow(G, N//n, P)
    assert pow(omega, n, P) == 1 and pow(omega, n//2, P) == P-1
    i = pow(omega, 4, P)
    assert i*i % P == P-1
    a = [P-1, 0, 1]
    b = scale([-i % P, 0, 1], i-1)
    c = scale([1, 0, 1], i)
    d = scale(mul([i, 0, 1], [1]+[0]*7+[1]), -pow(1+i, -1, P))
    v = [P-1]+[0]*15+[1]
    assert add(a, b) == c and mul(mul(a, b), mul(c, d)) == v
    assert [len(x)-1 for x in (a, b, c, d)] == [2, 2, 2, 10]
    roots = [[e for e in range(n) if evaluate(poly, pow(omega, e, P)) == 0]
             for poly in (a, b, c, d)]
    assert roots[:3] == [[0, 8], [2, 10], [4, 12]]
    assert sorted(sum(roots, [])) == list(range(n))
    assert {(-e) % n for e in roots[1]} == {6, 14} <= set(roots[3])
    reciprocal = [list(reversed(poly)) for poly in (a, b, c, d)]
    assert add(reciprocal[0], reciprocal[1]) == reciprocal[2]
    assert mul(mul(*reciprocal[:2]), mul(*reciprocal[2:])) == scale(v, -1)
    invariant_shifts = []
    for e in range(n):
        zeta = pow(omega, e, P)
        q = add(mul(a, shift(b, zeta)), mul(shift(a, zeta), b), -1)
        order = n//gcd(n, e)
        same_label = sum(1 for subset in roots[:3] for x in subset if (x+e) % n in subset)
        if q == [0]:
            invariant_shifts.append(e)
            assert degree % order == 0 and 10 % order == 0
            assert all(shift(poly, zeta) == poly for poly in (a, b, c, d))
        else:
            assert q[0] == 0 and len(q)-1 <= 2*degree-1
            count = sum(evaluate(q, pow(omega, x, P)) == 0 for x in range(n))
            assert same_label <= count <= 2*degree-2
    assert invariant_shifts == [0, 8]
    production_d = (N-10)//3
    assert 3*production_d+10 == N and gcd(gcd(N, production_d), 10) == 2
    genus = 3*production_d-2
    cs = production_d+2*(production_d-1)
    assert genus == N-12 == cs and production_d < P
    assert gcd(3, P-1) == 1
    cube_inverse = pow(3, -1, P-1)
    for value in (0, 1, i, G, a[-1]*b[-1]*c[-1] % P):
        assert pow(pow(value, cube_inverse, P), 3, P) == value
    print(json.dumps({'status': 'PASS_BOUNDED_CYCLOTOMIC_LOCATOR_CHECK',
                      'prime': P, 'small_n': n, 'small_root_exponents': roots,
                      'cyclic_shifts_checked': n, 'invariant_shifts': invariant_shifts,
                      'production_degree': production_d, 'maximum_common_lift_order': 2,
                      'production_same_label_bound': 2*production_d-2,
                      'production_cover_genus': genus, 'castelnuovo_severi_bound': cs,
                      'fp_cube_map_bijective': True, 'production_locator_constructed': False}, sort_keys=True))


if __name__ == '__main__':
    main()
