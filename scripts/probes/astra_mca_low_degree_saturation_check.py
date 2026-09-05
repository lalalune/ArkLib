#!/usr/bin/env python3
"""Exact low-degree controls; no production or six-pencil realization claim."""
import itertools
import json


def trim(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b, p, scale=1):
    return trim([(a[i] if i < len(a) else 0) + scale *
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))], p)


def mul(a, b, p):
    z = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            z[i+j] = (z[i+j] + x*y) % p
    return trim(z, p)


def evaluate(a, x, p):
    z = 0
    for coefficient in reversed(a):
        z = (z*x + coefficient) % p
    return z


def remainder(a, b, p):
    a, b = trim(a, p), trim(b, p)
    inverse = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        d, q = len(a)-len(b), a[-1]*inverse % p
        for j, x in enumerate(b):
            a[d+j] = (a[d+j]-q*x) % p
        a = trim(a, p)
    return a


def gcd(a, b, p):
    a, b = trim(a, p), trim(b, p)
    while b != [0]:
        a, b = b, remainder(a, b, p)
    return [(x*pow(a[-1], -1, p)) % p for x in a]


def determinant(matrix, p):
    matrix = [row[:] for row in matrix]
    value = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j] % p), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[pivot], matrix[j] = matrix[j], matrix[pivot]
            value = -value % p
        v = matrix[j][j] % p
        value = value*v % p
        inverse = pow(v, -1, p)
        for i in range(j+1, len(matrix)):
            q = matrix[i][j]*inverse % p
            matrix[i] = [(x-q*y) % p for x, y in zip(matrix[i], matrix[j])]
    return value


def resultant(f, g, b, p):
    assert len(f) <= b+1 and len(g) <= b+1
    rows = []
    for polynomial in (f, g):
        coefficients = list(reversed(polynomial + [0]*(b+1-len(polynomial))))
        for shift in range(b):
            rows.append([0]*shift + coefficients + [0]*(b-1-shift))
    return determinant(rows, p)


def cross(B, C, p):
    return [add(mul(B[j], C[k], p), mul(B[k], C[j], p), p, -1)
            for j, k in ((1, 2), (2, 0), (0, 1))]


def linear_combination(row, polynomials, p):
    z = [0]
    for coefficient, polynomial in zip(row, polynomials):
        z = add(z, polynomial, p, coefficient)
    return z


def geometry(B, C, b, p, exclude_conic=False):
    w = cross(B, C, p)
    assert max(map(len, w)) == 2*b+1
    assert gcd(gcd(w[0], w[1], p), w[2], p) == [1]
    receipt = {"b": b, "field": p, "basepoint_free": True}
    if exclude_conic:
        products = [mul(w[i], w[j], p) for i in range(3) for j in range(i, 3)]
        rows = [[f[d] if d < len(f) else 0 for f in products] for d in range(4*b+1)]
        # Retain a checkable coefficient minor, rather than only a rank label.
        for indices in itertools.combinations(range(4*b+1), 6):
            det = determinant([rows[i] for i in indices], p)
            if det:
                receipt["quadratic_product_minor"] = {"rows": indices, "determinant": det}
                break
        else:
            raise AssertionError("conic relation was not excluded")
    return w, receipt


def check_point(name, B, C, b, p, ci, expected):
    w, _ = geometry(B, C, b, p)
    locator = linear_combination(ci, w, p)
    assert len(locator) == 2*b+1  # No locator root at X-infinity.
    roots = [x for x in range(p) if evaluate(locator, x, p) == 0]
    assert len(roots) == 2*b  # Full splitting and squarefreeness.
    pivot = next(j for j, x in enumerate(ci) if x % p)
    projected_B, projected_C = [], []
    for j in range(3):
        if j == pivot:
            continue
        scale = -ci[j]*pow(ci[pivot], -1, p) % p
        projected_B.append(add(B[j], B[pivot], p, scale))
        projected_C.append(add(C[j], C[pivot], p, scale))
    directions = {}
    for x in roots:
        bvals = [evaluate(f, x, p) for f in projected_B]
        cvals = [evaluate(f, x, p) for f in projected_C]
        j = next(j for j in range(2) if bvals[j] or cvals[j])
        gamma = cvals[j]*pow(bvals[j], -1, p) % p if bvals[j] else None
        directions[gamma] = directions.get(gamma, 0)+1
    assert directions == expected, (name, directions)
    ratio = None
    for s, t in [(s, 1) for s in range(p)] + [(1, 0)]:
        f = add([t*x % p for x in projected_C[0]], projected_B[0], p, -s)
        g = add([t*x % p for x in projected_C[1]], projected_B[1], p, -s)
        actual = resultant(f, g, b, p)
        product = 1
        for gamma, multiplicity in directions.items():
            factor = t if gamma is None else s-gamma*t
            product = product*pow(factor, multiplicity, p) % p
        if product and ratio is None:
            ratio = actual*pow(product, -1, p) % p
            assert ratio
        assert actual == ratio*product % p if ratio is not None else actual == 0
    assert p > 2*b and ratio is not None
    return {"name": name, "field": p, "ci": ci, "roots": roots,
            "direction_multiplicities": sorted(directions.items()),
            "projective_evaluations": p+1, "resultant_scalar": ratio}


def main():
    cases, geometries = [], []
    p = 101
    B, C = [[1], [0, 1], [0]], [[0], [1], [0, 1]]
    cases.append(check_point("b1_unsaturated", B, C, 1, p, [1, 0, -1], {1: 1, 100: 1}))

    a, b0, c0 = [[2, -3, 1], [12, -7, 1], [30, -11, 1]]
    B = [trim(f, p) for f in (a, b0, c0)]
    C = [[(j+1)*x % p for x in f] for j, f in enumerate(B)]
    _, geo = geometry(B, C, 2, p, True)
    geometries.append({"name": "b2_sharp_three_birational", **geo})
    assert determinant([a, b0, c0], p) == 32
    for i in range(3):
        ci = [int(j == i) for j in range(3)]
        directions = {j+1: 2 for j in range(3) if j != i}
        cases.append(check_point(f"b2_sharp_point_{i}", B, C, 2, p, ci, directions))

    B, C = [[1], [0, 0, 1], [0]], [[0], [1], [0, 0, 1]]
    _, geo = geometry(B, C, 2, p)
    geometries.append({"name": "b2_degree_two_cover", **geo})
    values = [-pow(x*x, -1, p) % p for x in range(1, 5)]
    points = []
    for i, j in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]:
        r, s = values[i], values[j]
        ci = [r*s % p, -(r+s) % p, 1]
        points.append(ci)
        cases.append(check_point(f"b2_cover_point_{i}_{j}", B, C, 2, p, ci, {r: 2, s: 2}))
    assert len({tuple(ci) for ci in points}) == 5
    assert any(determinant(list(rows), p) for rows in itertools.combinations(points, 3))

    p = 11
    B, C = [[1], [0, 1], [6, 0, 3, 10]], [[0], [0, 1, 0, 1], [5, 4, 2, 5]]
    _, geo = geometry(B, C, 3, p, True)
    geometries.append({"name": "b3_one_saturated_birational", **geo})
    case = check_point("b3_one_saturated", B, C, 3, p, [1, 0, 0], {2: 2, 5: 2, 10: 2})
    assert case["resultant_scalar"] == 6
    cases.append(case)
    print(json.dumps({"status": "PASS_LOW_DEGREE_CONTROLS", "cases": cases,
                      "geometry": geometries,
                      "projective_evaluations": sum(c["projective_evaluations"] for c in cases),
                      "five_square_b3_example": False, "production_claim": False}, sort_keys=True))


if __name__ == "__main__":
    main()
