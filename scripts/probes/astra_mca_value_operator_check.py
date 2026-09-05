#!/usr/bin/env python3
"""Cyclotomic product operators and exact received-word covariance controls."""

from itertools import product
import json

import astra_mca_single_hole_locator_check as poly


P = poly.P
OMEGA = poly.OMEGA
D = tuple(x for x in OMEGA if x != 1)
K = 4
A = 5


def reciprocal(f):
    padded = tuple(f)+(0,)*(K-len(f))
    return poly.trim(tuple(reversed(padded)))


def product_roots(roots):
    value = 1
    for x in roots:
        value = value*x % P
    return value


def record(f, word, evaluations):
    errors = frozenset(x for x in D if evaluations[x] != word[x])
    if len(D)-len(errors) < A:
        return None
    f = poly.trim(f)
    lam = poly.locator(errors)
    tau = product_roots(errors)
    assert tau == (-1)**len(errors)*lam[0] % P
    assert pow(tau, len(OMEGA), P) == 1
    return (f, poly.evaluate(f, 1), errors, tau)


def main():
    original = {x:{2:1, 15:11}.get(x, 0) for x in D}
    jword = {x:pow(x, K-1, P)*original[pow(x, -1, P)] % P for x in D}
    translated = {x:(original[x]+3) % P for x in D}
    e0 = frozenset((2, 4))
    e1 = frozenset(-x % P for x in e0)
    z = frozenset(D)-e0-e1
    h = poly.locator(z)
    antipodal = {x:poly.evaluate(h, x) if x in e0 else 0 for x in D}
    assert e0.isdisjoint(e1) and product_roots(e0) == product_roots(e1)
    assert h == (4, 4, 1, 1) and poly.evaluate(h, 1) == 10
    words = {'original':original, 'reciprocal':jword,
             'translated':translated, 'antipodal':antipodal}
    lists = {name:[] for name in words}
    for coefficients in product(range(P), repeat=K):
        evaluations = {x:poly.evaluate(coefficients, x) for x in D}
        for name, word in words.items():
            candidate = record(coefficients, word, evaluations)
            if candidate is not None:
                lists[name].append(candidate)
    assert all(len(items) == 3 for items in lists.values())
    assert {f for f, _, _, _ in lists['original']} == {
        (0,), (3, 3, 5, 5), (8, 8, 8, 8)}
    assert {f for f, _, _, _ in lists['antipodal']} == {
        (0,), (4, 4, 1, 1), (5, 1, 6, 14)}
    assert {tau for _, _, _, tau in lists['antipodal']} == {8}
    assert {value for _, value, _, _ in lists['antipodal']} == {0, 9, 10}
    transformed = {
        (reciprocal(f), value, frozenset(pow(x, -1, P) for x in errors), pow(tau, -1, P))
        for f, value, errors, tau in lists['original']}
    assert transformed == set(lists['reciprocal'])
    shifted = {(poly.add(f, (3,)), (value+3) % P, errors, tau)
               for f, value, errors, tau in lists['original']}
    assert shifted == set(lists['translated'])
    discrepancy = poly.add(poly.interpolate(D, jword),
                           poly.scale(-1, poly.interpolate(D, original)))
    assert discrepancy == (0, 0, 15, 15, 15, 15)
    assert poly.degree(discrepancy) >= K
    assert any(reciprocal(f) not in {g for g, _, _, _ in lists['original']}
               for f, _, _, _ in lists['original'])
    assert all({zeta*x % P for x in D} != set(D) for zeta in OMEGA if zeta != 1)

    # On the original fixture the product labels happen to be distinct.
    # Interpolation then supplies the conditional degree-n resultant.
    labels = tuple(tau for _, _, _, tau in lists['original'])
    label_values = {tau:value for _, value, _, tau in lists['original']}
    assert len(label_values) == 3
    interpolation = poly.interpolate(labels, label_values)
    resultant = poly.locator(poly.evaluate(interpolation, x) for x in OMEGA)
    assert poly.degree(resultant) == len(OMEGA)
    assert all(poly.evaluate(resultant, value) == 0
               for _, value, _, _ in lists['original'])

    # T is scalar in this second exact algebra, whereas M is not scalar.
    # Every multiplicative-character product T^j is therefore scalar too.
    for j in range(len(OMEGA)):
        assert len({pow(tau, j, P) for _, _, _, tau in lists['antipodal']}) == 1
    value_minimal = poly.locator(sorted({value for _, value, _, _ in lists['antipodal']}))
    assert poly.degree(value_minimal) == 3
    # The valid identity for T is not an identity for M.
    assert any(pow(value, len(OMEGA), P) != 1
               for _, value, _, _ in lists['translated'])

    b = 178956971
    n, e, k = 6*b-2, 2*b-2, 3*b-1
    assert n == 2**30 and e > 0 and e % 2 == 0
    assert e <= (n-2)//2 and (n-1)-2*e < k <= (n-1)-e
    assert (n-1)-2*e == 357913943
    print(json.dumps({
        'status':'PASS_CYCLOTOMIC_PRODUCT_OPERATOR_OBSTRUCTION',
        'field':P, 'domain_order':len(OMEGA), 'agreement':A,
        'code_polynomials_enumerated':P**K, 'fixed_received_words':len(words),
        'original_product_label_interpolant':interpolation,
        'conditional_resultant_degree':poly.degree(resultant),
        'antipodal_complete_list':[f for f, _, _, _ in lists['antipodal']],
        'antipodal_distinct_values':sorted({value for _, value, _, _ in lists['antipodal']}),
        'antipodal_product_operator_scalar':8,
        'antipodal_value_minimal_polynomial':value_minimal,
        'reciprocal_word_discrepancy_polynomial':discrepancy,
        'production_two_witness_difference_degree':(n-1)-2*e,
        'production_bound_disproved':False, 'production_bound_proved':False,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
