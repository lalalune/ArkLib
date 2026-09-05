#!/usr/bin/env python3
"""Exact private-cubic controls; no production or MCA realization claim.

Standard library only. The checker verifies integer polynomial identities,
rational specializations, and finite point orders. The accompanying note
uses the standard torsion-reduction and elliptic-height theorems separately;
neither those theorems nor the general normal-form proof are formalized here.
"""

from fractions import Fraction
import json


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b, scale=1):
    result = [a[i] if i < len(a) else 0
              for i in range(max(len(a), len(b)))]
    for i, value in enumerate(b):
        result[i] += scale * value
    return trim(result)


def mul(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return trim(result)


def cube(a):
    return mul(mul(a, a), a)


def remainder(a, b):
    a, b = trim(map(Fraction, a)), trim(map(Fraction, b))
    if b == [0]:
        raise ZeroDivisionError("zero polynomial")
    while a != [0] and len(a) >= len(b):
        shift, factor = len(a) - len(b), a[-1] / b[-1]
        for i, value in enumerate(b):
            a[shift + i] -= factor * value
        a = trim(a)
    return a


def gcd(a, b):
    a, b = trim(a), trim(b)
    while b != [0]:
        a, b = b, remainder(a, b)
    return [value / a[-1] for value in a]


def derivative(a):
    return trim([i * a[i] for i in range(1, len(a))] or [0])


def sparse_add(a, b, scale=1):
    result = a.copy()
    for monomial, value in b.items():
        result[monomial] = result.get(monomial, 0) + scale * value
    return {key: value for key, value in result.items() if value}


def sparse_mul(a, b):
    result = {}
    for exponents_a, x in a.items():
        for exponents_b, y in b.items():
            key = tuple(i + j for i, j in zip(exponents_a, exponents_b))
            result[key] = result.get(key, 0) + x * y
    return {key: value for key, value in result.items() if value}


def sparse_power(a, n):
    result = {(0, 0, 0): 1}
    for _ in range(n):
        result = sparse_mul(result, a)
    return result


def check_birational_identities():
    """Verify forward, inverse, and composition identities over Z[q,u,v]."""
    one = {(0, 0, 0): 1}
    q, u, v = ({(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1})
    q2, q4, q6 = (sparse_power(q, n) for n in (2, 4, 6))
    delta = sparse_add(q6, one, -1)
    d = sparse_add(u, sparse_mul(q2, v), -1)
    a = sparse_add(sparse_mul(q4, u), v, -1)
    cubic = sparse_add(sparse_add(sparse_power(u, 3), u, -1),
                       sparse_add(sparse_power(v, 3), sparse_mul(q2, v), -1), -1)
    # Substitute x=a/d, y=delta/d into the Weierstrass equation.
    numerator = sparse_add(sparse_mul(sparse_power(delta, 2), d),
                           sparse_power(a, 3), -1)
    numerator = sparse_add(numerator,
                           sparse_mul(q2, sparse_mul(a, sparse_power(d, 2))), 3)
    numerator = sparse_add(numerator,
                           sparse_mul(sparse_add(q6, one), sparse_power(d, 3)), -1)
    assert sparse_add(numerator, sparse_mul(sparse_power(delta, 2), cubic)) == {}

    # The same ring now has variables (q,x,y). Verify the inverse substitution.
    x, y = u, v
    un = sparse_add(sparse_mul(q2, x), one, -1)
    vn = sparse_add(x, q4, -1)
    weierstrass = sparse_add(sparse_power(y, 2), sparse_power(x, 3), -1)
    weierstrass = sparse_add(weierstrass, sparse_mul(q2, x), 3)
    weierstrass = sparse_add(weierstrass, sparse_add(q6, one), -1)
    inverse_numerator = sparse_add(sparse_power(un, 3),
                                   sparse_mul(un, sparse_power(y, 2)), -1)
    inverse_numerator = sparse_add(inverse_numerator, sparse_power(vn, 3), -1)
    inverse_numerator = sparse_add(inverse_numerator,
                                   sparse_mul(q2, sparse_mul(vn, sparse_power(y, 2))))
    assert sparse_add(inverse_numerator, sparse_mul(delta, weierstrass)) == {}
    assert sparse_add(un, sparse_mul(q2, vn), -1) == delta
    assert sparse_add(sparse_mul(q4, un), vn, -1) == sparse_mul(delta, x)
    assert sparse_add(sparse_mul(q2, a), d, -1) == sparse_mul(delta, u)
    assert sparse_add(a, sparse_mul(q4, d), -1) == sparse_mul(delta, v)

    # Discriminant -16*(4*a4^3+27*a6^2) = -432*(q^6-1)^2.
    a4 = {key: -3 * value for key, value in q2.items()}
    a6 = sparse_add(q6, one)
    discriminant = sparse_add(
        {key: -64 * value for key, value in sparse_power(a4, 3).items()},
        sparse_power(a6, 2), -432)
    assert discriminant == {key: -432 * value
                            for key, value in sparse_power(delta, 2).items()}
    assert discriminant  # The generic cubic is smooth.


def section(t):
    q = (7 * t * t - 10 * t - 1) / (14 * t * t - 6 * t - 4)
    u = (-14 * t * t + 2 * t) / (14 * t * t - 6 * t - 4)
    v = (-7 * t * t - 6 * t + 1) / (14 * t * t - 6 * t - 4)
    x = (q ** 4 * u - v) / (u - q * q * v)
    y = (q ** 6 - 1) / (u - q * q * v)
    assert y * y == x ** 3 - 3 * q * q * x + q ** 6 + 1
    return q, x, y


def residue(x, p):
    return x.numerator * pow(x.denominator, -1, p) % p


def ec_add(a, b, p):
    if a is None:
        return b
    if b is None:
        return a
    x, y = a
    u, v = b
    if x == u and (y + v) % p == 0:
        return None
    slope = ((3 * x * x - 48) * pow(2 * y, -1, p) if a == b
             else (v - y) * pow(u - x, -1, p)) % p
    r = (slope * slope - x - u) % p
    return r, (slope * (x - r) - y) % p


def order(point, p):
    result = None
    for n in range(1, 2 * p + 3):
        result = ec_add(result, point, p)
        if result is None:
            return n
    raise AssertionError("point order not found within Hasse bound")


def main():
    check_birational_identities()
    # Ascending coefficient arrays; these identities hold over the integers.
    t1, t2 = [-1, -10, 7], [-4, -6, 14]
    u, v = [0, 2, -14], [1, -6, -7]
    assert len(t1) == len(t2) == 3 and gcd(t1, t2) == [1]
    assert gcd(t1, derivative(t1)) == gcd(t2, derivative(t2)) == [1]
    assert add(add(cube(u), mul(mul(t2, t2), u), -1),
               add(cube(v), mul(mul(t1, t1), v), -1), -1) == [0]
    assert add([4 * c for c in t1], t2, -1) == [0, -34, 14]
    sigma_num, sigma_den = [17, -7], [7, -49]

    def substitute_quadratic(f):
        return add(add([f[0] * c for c in mul(sigma_den, sigma_den)],
                       mul(sigma_num, sigma_den), f[1]),
                   mul(sigma_num, sigma_num), f[2])

    assert add(mul(substitute_quadratic(t1), t2),
               mul(substitute_quadratic(t2), t1), -1) == [0]
    sigma_twice_num = add([17 * c for c in sigma_den], sigma_num, -7)
    sigma_twice_den = add([7 * c for c in sigma_den], sigma_num, -49)
    assert add(sigma_twice_num, mul([0, 1], sigma_twice_den), -1) == [0]
    assert add(sigma_num, mul([0, 1], sigma_den), -1) != [0]

    q, x, y = section(Fraction(0))
    q_conjugate, x_conjugate, y_conjugate = section(Fraction(17, 7))
    assert q == q_conjugate == Fraction(1, 4) and q ** 6 != 1
    point = (x * 16, y * 64)
    conjugate = (x_conjugate * 16, y_conjugate * 64)
    assert point == (Fraction(256), Fraction(-4095))
    assert conjugate == (Fraction(-47, 4), Fraction(441, 8))
    for x, y in (point, conjugate):
        assert y * y == x ** 3 - 48 * x + 4097

    checks = []
    for p, expected_point, expected_difference in [(11, 8, 16), (17, 13, 1)]:
        assert (4 * (-48) ** 3 + 27 * 4097 ** 2) % p != 0
        pp = tuple(residue(x, p) for x in point)
        negative_conjugate = (residue(conjugate[0], p), residue(-conjugate[1], p))
        difference = ec_add(pp, negative_conjugate, p)
        assert order(pp, p) == expected_point
        assert order(difference, p) == expected_difference
        checks.append({"prime": p, "section_order": expected_point,
                       "section_minus_conjugate_order": expected_difference})

    b = 178956971
    m = 2 * b - 2
    lower, upper = (m - 3) // 2, m - 2  # ceil((m-4)/2), m-2.
    assert (m, lower, upper) == (357913940, 178956968, 357913938)
    print(json.dumps({
        "status": "PASS_PRIVATE_CUBIC_SURFACE_CONTROLS",
        "symbolic_birational_identities": True,
        "symbolic_discriminant_identity": True,
        "exact_integer_section_identity": True,
        "T1": t1, "T2": t2, "U": u, "V": v, "R": [1],
        "quadratic_cofactors_coprime_squarefree": True, "base_map_degree": 2,
        "base_involution": {"numerator": sigma_num, "denominator": sigma_den},
        "good_reduction_checks": checks,
        "production_normal_form_degree_interval": [lower, upper],
        "external_mathematical_inputs": ["prime-to-p torsion reduction",
                                         "positive elliptic height modulo torsion"],
        "general_normal_form_lean_formalized": False,
        "squarefree_private_locators_verified": False,
        "saturation_verified": False, "cyclotomic_product_verified": False,
        "production_characteristic_verified": False,
        "actual_mca_counterexample": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
