#!/usr/bin/env python3
"""Bounded Sylvester/product checks; not a production six-pencil witness."""
import json

P = 101


def add(a, b, scale=1):
    return [((a[i] if i < len(a) else 0) +
             scale*(b[i] if i < len(b) else 0)) % P
            for i in range(max(len(a), len(b)))]


def mul(a, b):
    result = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] = (result[i+j]+x*y) % P
    return result


def evaluate(a, x):
    value = 0
    for coefficient in reversed(a):
        value = (value*x+coefficient) % P
    return value


def determinant(matrix):
    matrix = [row[:] for row in matrix]
    result = 1
    for column in range(len(matrix)):
        pivot = next((i for i in range(column, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            result = -result % P
        value = matrix[column][column]
        result = result*value % P
        inverse = pow(value, -1, P)
        for i in range(column+1, len(matrix)):
            ratio = matrix[i][column]*inverse % P
            matrix[i] = [(x-ratio*y) % P for x, y in zip(matrix[i], matrix[column])]
    return result


def resultant(f, g, degree):
    # Pad to the DECLARED binary degree, including specialization at infinity.
    f = list(reversed(f+[0]*(degree+1-len(f))))
    g = list(reversed(g+[0]*(degree+1-len(g))))
    assert len(f) == len(g) == degree+1
    rows = []
    for polynomial in (f, g):
        for shift in range(degree):
            rows.append([0]*shift+polynomial+[0]*(degree-1-shift))
    return determinant(rows)


def fixture(roots):
    degree = len(roots)//2
    locator = [1]
    for root in roots:
        locator = mul(locator, [-root % P, 1])
    # B=(0,1,X^b), C=(1,C1,C2); C2-X^b*C1=-locator.
    c1 = locator[degree:]
    c2 = [-x % P for x in locator[:degree]]
    return degree, [1], [0]*degree+[1], c1, c2


def check(name, roots, row, expected_multiplicities=None):
    degree, b1, b2, c1, c2 = row
    assert len(roots) == 2*degree and len(set(roots)) == len(roots)
    locator = add(mul(b1, c2), mul(b2, c1), -1)
    assert len(locator) == 2*degree+1 and locator[-1] != 0
    assert all(evaluate(locator, x) == 0 for x in roots)
    directions = {}
    for x in roots:
        bx, cx = evaluate(b1, x), evaluate(c1, x)
        assert bx or cx
        gamma = cx*pow(bx, -1, P) % P if bx else None
        directions[gamma] = directions.get(gamma, 0)+1
    if expected_multiplicities is not None:
        assert directions == expected_multiplicities, (name, directions)
    reference = None
    parameters = [(s, 1) for s in range(P)]+[(1, 0)]
    for s, t in parameters:
        f = add([t*x % P for x in c1], b1, -s)
        g = add([t*x % P for x in c2], b2, -s)
        actual = resultant(f, g, degree)
        product = 1
        for x in roots:
            product = product*(t*evaluate(c1, x)-s*evaluate(b1, x)) % P
        if product and reference is None:
            reference = actual*pow(product, -1, P) % P
            assert reference
        if reference is not None:
            assert actual == reference*product % P
        else:
            assert actual == 0
        # Change annihilator basis by [[2,3],[5,7]], determinant -1.
        changed = resultant(add([2*x % P for x in f], g, 3),
                            add([5*x % P for x in f], g, 7), degree)
        assert changed == pow(-1, degree, P)*actual % P
    assert reference is not None and 2*degree < P
    # >2b scalar evaluations determine the degree<=2b identity, so this checks
    # coefficients/multiplicities too, not merely the locations of zeros.
    return {"name": name, "b": degree, "projective_parameters": len(parameters),
            "finite_direction_multiplicities": sorted(v for k, v in directions.items() if k is not None),
            "pole_slots": directions.get(None, 0)}


def main():
    rows = []
    for degree in range(1, 5):
        roots = list(range(1, 2*degree+1))
        rows.append(check(f"consecutive_b{degree}", roots, fixture(roots)))
    roots = [1, P-1, 2, P-2]
    saturated = (2, [1], [0, 0, 1], [0, 0, 1], [-4 % P, 0, 5])
    rows.append(check("two_finite_pairs", roots, saturated, {1: 2, 4: 2}))
    degree, b1, b2, c1, c2 = saturated
    # Replace (B,C) by (C-B,B): old gamma=1 becomes the true infinity slot.
    with_poles = (degree, add(c1, b1, -1), add(c2, b2, -1), b1, b2)
    rows.append(check("one_pair_at_infinity", roots, with_poles, {None: 2, pow(3, -1, P): 2}))
    assert rows[1]["finite_direction_multiplicities"] == [1, 1, 1, 1]
    print(json.dumps({"status": "PASS_BOUNDED_RESULTANT_IDENTITY", "field": P,
                      "cases": rows, "production_witness": False,
                      "six_pencil_realization_claimed": False}, sort_keys=True))


if __name__ == "__main__":
    main()
