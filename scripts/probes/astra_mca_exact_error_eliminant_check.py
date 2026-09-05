#!/usr/bin/env python3
"""Reduced exact-error factor algebras and value polynomials; no production bound."""

from collections import Counter
from itertools import combinations, product
import json

import astra_mca_single_hole_locator_check as poly


P = poly.P
OMEGA = poly.OMEGA
HOLE = 1
K = 4
NODES = tuple(x for x in OMEGA if x != HOLE)
DOMAIN = poly.locator(NODES)
N = len(NODES)


def coefficient(f, j):
    return f[j] if j < len(f) else 0


def derivative(f):
    return poly.trim([j*f[j] for j in range(1, len(f))])


def monic_product(roots):
    return poly.locator(roots)


def factor_points(max_degree):
    points = []
    for d in range(max_degree+1):
        for roots in combinations(NODES, d):
            lam = poly.locator(roots)
            complement, residual = poly.divide(DOMAIN, lam)
            assert residual == (0,)
            columns = [(0,)*j+complement for j in range(d)]
            columns += [(0,)*j+lam for j in range(N-d)]
            jacobian = [[coefficient(column, j) for column in columns]
                        for j in range(N)]
            assert poly.rank(jacobian) == N
            assert poly.multiply(lam, complement) == DOMAIN
            for x in NODES:
                selector = poly.evaluate(derivative(lam), x)*poly.evaluate(complement, x)
                selector = selector*pow(poly.evaluate(derivative(DOMAIN), x), -1, P) % P
                assert selector == int(x in roots)
            points.append((d, roots, lam, complement))
    return points


def exact_points(word, points):
    received = poly.interpolate(NODES, word)
    records = []
    padded = Counter()
    for d, roots, lam, complement in points:
        quotient, remainder = poly.divide(poly.multiply(lam, received), DOMAIN)
        assert poly.degree(quotient) < d
        if poly.degree(remainder) >= K+d:
            continue
        f, residual = poly.divide(remainder, lam)
        assert residual == (0,) and poly.degree(f) < K
        assert poly.add(received, poly.scale(-1, f)) == poly.multiply(quotient, complement)
        errors = frozenset(x for x in NODES if poly.evaluate(f, x) != word[x])
        saturation = 1
        for x in roots:
            saturation = saturation*poly.evaluate(quotient, x) % P
            left = poly.evaluate(derivative(lam), x)*(word[x]-poly.evaluate(f, x)) % P
            right = poly.evaluate(quotient, x)*poly.evaluate(derivative(DOMAIN), x) % P
            assert left == right
        assert bool(saturation) == (errors == frozenset(roots))
        if not saturation:
            padded[d] += 1
            continue
        value = poly.evaluate(remainder, HOLE)*poly.evaluate(complement, HOLE)
        value = value*pow(len(OMEGA), -1, P) % P
        assert value == poly.evaluate(f, HOLE)
        records.append((d, f, errors, value))
    assert len({f for _, f, _, _ in records}) == len(records)
    return records, padded


def check_value_operator(records):
    values = [value for _, _, _, value in records]
    multiplicities = Counter(values)
    characteristic = monic_product(values)
    minimal = monic_product(sorted(multiplicities))
    distinct_count = len(multiplicities)
    assert poly.degree(characteristic) == len(records)
    assert poly.degree(minimal) == distinct_count
    assert all(poly.evaluate(minimal, value) == 0 for value in values)
    if values:
        # Independence proves that no polynomial of lower degree annihilates
        # multiplication by these diagonal values, including repeated values.
        krylov = [[pow(value, j, P) for j in range(distinct_count)] for value in values]
        assert poly.rank(krylov) == distinct_count
    return {
        'decoded_polynomials':len(records),
        'distinct_values':distinct_count,
        'characteristic_polynomial':characteristic,
        'minimal_polynomial':minimal,
        'value_multiplicities':dict(sorted(multiplicities.items())),
    }


def truncated_resultant_dual_control():
    # A nonzero infinitesimal coefficient change survives the two low
    # coefficients of Res(P_D,Lambda+Z), before the decoding equations.
    r, s = NODES[:2]
    lam = poly.locator((r, s))
    slope = 2*pow(r-s, -1, P) % P
    tangent = ((1-slope*r) % P, slope)
    assert poly.evaluate(tangent, r) == 1 and poly.evaluate(tangent, s) == P-1

    def dual_add(a, b):
        return ((a[0]+b[0]) % P, (a[1]+b[1]) % P)

    def dual_mul(a, b):
        return (a[0]*b[0] % P, (a[0]*b[1]+a[1]*b[0]) % P)

    out = [(1, 0)]
    for x in NODES:
        term = (poly.evaluate(lam, x), poly.evaluate(tangent, x))
        following = [(0, 0)]*(len(out)+1)
        for j, c in enumerate(out):
            following[j] = dual_add(following[j], dual_mul(c, term))
            following[j+1] = dual_add(following[j+1], c)
        out = following
    assert out[0] == out[1] == (0, 0) and tangent != (0, 0)


def main():
    word = {x:{2:1, 15:11}.get(x, 0) for x in NODES}
    zero = {x:0 for x in NODES}
    enumerated = []
    zero_enumerated = []
    # This enumeration does not use locators, interpolation, or saturation.
    for coefficients in product(range(P), repeat=K):
        evaluations = {x:poly.evaluate(coefficients, x) for x in NODES}
        errors = frozenset(x for x in NODES if evaluations[x] != word[x])
        if N-len(errors) >= 4:
            f = poly.trim(coefficients)
            enumerated.append((len(errors), f, errors, poly.evaluate(f, HOLE)))
        if sum(evaluations[x] == 0 for x in NODES) >= 4:
            zero_enumerated.append(poly.trim(coefficients))
    assert len(enumerated) == 23 and zero_enumerated == [(0,)]
    points = factor_points(3)
    assert len(points) == 64
    records, padded = exact_points(word, points)
    assert set(records) == set(enumerated)
    assert padded == Counter({3:15})
    high = [record for record in records if record[0] <= 2]
    assert set(high) == {record for record in enumerated if record[0] <= 2}
    high_result = check_value_operator(high)
    low_result = check_value_operator(records)
    assert high_result['decoded_polynomials'] == high_result['distinct_values'] == 3
    assert high_result['minimal_polynomial'] == (0, 2, 3, 1)
    assert low_result['decoded_polynomials'] == 23 and low_result['distinct_values'] == 15
    zero_records, zero_padding = exact_points(zero, points)
    assert [f for _, f, _, _ in zero_records] == zero_enumerated
    assert zero_records == [(0, (0,), frozenset(), 0)]
    assert sum(zero_padding.values()) == len(points)-1
    truncated_resultant_dual_control()
    b = 178956971
    production_n, production_k, production_e = 6*b-2, 3*b-1, 2*b-2
    assert production_n == 2**30
    tangent_lower_bound = 2*production_e+production_k-(production_n-1)-1
    assert tangent_lower_bound == b-3 == 178956968
    print(json.dumps({
        'status':'PASS_REDUCED_EXACT_ERROR_ELIMINANT',
        'field':P, 'domain_order':len(OMEGA), 'code_dimension':K,
        'polynomials_independently_enumerated':P**K,
        'factor_points_and_invertible_jacobians_checked':len(points),
        'agreement_5':high_result, 'agreement_4_algebra_control':low_result,
        'padded_points_removed_at_degree_3':padded[3],
        'zero_word_exact_degree':zero_records[0][0],
        'zero_word_padded_points_removed':sum(zero_padding.values()),
        'truncated_resultant_nonzero_dual_tangent_verified':True,
        'production_truncated_scheme_tangent_lower_bound':tangent_lower_bound,
        'production_value_degree_bound_proved':False,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
