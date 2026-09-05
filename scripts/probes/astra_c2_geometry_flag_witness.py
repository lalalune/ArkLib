#!/usr/bin/env python3
"""A regular polynomial-solution witness for the binding ordinary C2 flag.

This verifies polynomial identities and support over the actual characteristic.
It does not construct membership in a universal interpolation kernel or a
large selected family. The accompanying unformalized proof note supplies
geometric irreducibility and the general local-transversality argument.
"""

from itertools import product

CHAR = 2130706433
ZERO = (0, 0, 0, 0)


def clean(poly):
    return {e: c % CHAR for e, c in poly.items() if c % CHAR}


def const(c):
    return clean({ZERO: c})


def var(i):
    return {tuple(int(i == j) for j in range(4)): 1}


def add(*polys):
    result = {}
    for poly in polys:
        for e, c in poly.items():
            result[e] = result.get(e, 0) + c
    return clean(result)


def mul(left, right):
    result = {}
    for (a, c), (b, d) in product(left.items(), right.items()):
        e = tuple(x + y for x, y in zip(a, b))
        result[e] = result.get(e, 0) + c * d
    return clean(result)


def power(poly, n):
    result = const(1)
    while n:
        if n & 1:
            result = mul(result, poly)
        n //= 2
        if n:
            poly = mul(poly, poly)
    return result


def deriv(poly, i):
    result = {}
    for e, c in poly.items():
        if e[i]:
            t = tuple(x - int(j == i) for j, x in enumerate(e))
            result[t] = c * e[i]
    return clean(result)


def compose(poly, values):
    powers = {}
    result = {}
    for e, c in poly.items():
        term = const(c)
        for i, n in enumerate(e):
            key = (i, n)
            if key not in powers:
                powers[key] = power(values[i], n)
            term = mul(term, powers[key])
        result = add(result, term)
    return result


def weight(poly, weights):
    return max(sum(a * b for a, b in zip(e, weights)) for e in poly)


def main():
    x, y, r, z = (var(i) for i in range(4))
    a = add(y, mul(const(-1), x))
    b = add(r, const(-1))
    f = add(b, mul(const(-1), mul(x, a)), mul(const(-1), z),
            power(a, 47), power(b, 10), power(z, 2364))
    h = deriv(f, 2)

    # The actual regular polynomial solution is f_selected(X)=X, gamma=0.
    point = (x, x, const(1), {})
    assert compose(f, point) == {}
    assert compose(h, point) == const(1)

    # This triangular change is a polynomial-ring automorphism, with inverse
    # Y -> Y-X, R -> R-1. The displayed image is primitive linear in X.
    image = compose(f, (x, add(y, x), add(r, const(1)), z))
    expected = add(r, mul(const(-1), mul(x, y)), mul(const(-1), z),
                   power(y, 47), power(r, 10), power(z, 2364))
    assert image == expected
    assert weight(image, (1, 0, 0, 0)) == 1
    x_coefficient = {tuple(e[j] - int(j == 0) for j in range(4)): c
                     for e, c in image.items() if e[0] == 1}
    assert x_coefficient == mul(const(-1), y)
    constant_mod_y = {e: c for e, c in image.items() if e[0] == 0 and e[1] == 0}
    assert constant_mod_y == add(r, power(r, 10), mul(const(-1), z), power(z, 2364))
    assert constant_mod_y  # Y does not divide the constant coefficient.

    # Independent differentiation and second-order recurrence checks. For
    # DA=XA+Z modulo (A,Z)^2, D^n A = a_n(X) A + b_n(X) Z modulo that ideal.
    aa, bb = [const(1), x], [{}, const(1)]
    for n in range(1, 20):
        aa.append(add(mul(x, aa[n]), mul(const(n), aa[n-1])))
        bb.append(add(mul(x, bb[n]), mul(const(n), bb[n-1])))
        assert aa[n+1] == add(deriv(aa[n], 0), mul(x, aa[n]))
        assert bb[n+1] == add(deriv(bb[n], 0), aa[n])
    factorial = 1
    for n in range(1, 20):
        factorial = factorial * n % CHAR
        determinant = add(mul(aa[n], bb[n+1]), mul(const(-1), mul(aa[n+1], bb[n])))
        assert determinant == const((-1) ** n * factorial)

    # Evaluate the same recurrence at X=0 through the actual tail index.
    # This is a finite witness of a nonzero determinant polynomial; it is
    # NOT a computation of all coefficients of the production-size tails.
    tail_index = 131072
    am, an, bm, bn = 1, 0, 0, 1
    factorial = 1
    for n in range(1, tail_index + 1):
        anext, bnext = n * am % CHAR, n * bm % CHAR
        factorial = factorial * n % CHAR
        if n == tail_index:
            determinant = (an * bnext - anext * bn) % CHAR
            assert determinant == (-1) ** n * factorial % CHAR
            assert determinant != 0
        am, an, bm, bn = an, anext, bn, bnext

    s = weight(f, (0, 0, 1, 0))
    ys = weight(f, (0, 1, 1, 0))
    total = weight(f, (0, 1, 1, 1))
    contact = weight(f, (1, 131071, 131070, 0))
    assert (s, ys, total) == (10, 47, 2364)
    assert (s, ys - s, total - ys) == (10, 37, 2317)
    assert contact == 6160337
    print(f"characteristic: {CHAR}")
    print(f"nonzero_monomials: {len(f)}")
    print(f"cumulative_R_Y_T: {(s, ys, total)}")
    print(f"raw_r_v_z: {(s, ys-s, total-ys)}")
    print(f"contact_weight: {contact}")
    print("regular_solution: gamma=0, selected(X)=X, partial_R(F)=1")
    print("verified_coordinate_change: primitive linear form over K")
    print("geometric_irreducibility_and_transversality: proof note, not Lean checked")
    print(f"tail_index: {tail_index}")
    print(f"next_tail_linear_determinant_at_X_zero: {determinant}")
    print("small_polynomial_recurrence_checks: n=1..19 PASS")
    print("PASS: finite identities and recurrence checks; no large-family or kernel claim")


if __name__ == "__main__":
    main()
