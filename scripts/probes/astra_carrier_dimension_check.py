#!/usr/bin/env python3
"""Exact finite controls for carrier dimension/degree incidence bounds."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb
import json

import astra_mca_single_hole_locator_check as poly


def evaluate(f, x, p):
    value = 0
    for coefficient in reversed(f):
        value = (value*x+coefficient) % p
    return value


def scalar_ratio(n, k, a, r):
    assert 1 <= k <= a <= n and 0 <= r <= k
    return Fraction(comb(n-k+r, r), comb(a-k+r, r))


def mca_ratio(n, k, t, r):
    assert 1 <= k < t <= n and 0 <= r <= k+1
    if r == 0:
        return Fraction(1)
    answer = Fraction(n-t+1)
    for j in range(2, r+1):
        answer *= Fraction(n-k-1+j, t-k-1+j)
    return answer


def maximum_list_on_carrier(p, nodes, candidates, agreements):
    assert len(set(candidates)) == len(candidates)
    n = len(nodes)
    counts = Counter()
    for f in candidates:
        word = tuple(evaluate(f, x, p) for x in nodes)
        for errors in range(n-agreements+1):
            for support in combinations(range(n), errors):
                alternatives = [tuple(v for v in range(p) if v != word[i]) for i in support]
                for values in product(*alternatives):
                    center = list(word)
                    for i, value in zip(support, values):
                        center[i] = value
                    counts[tuple(center)] += 1
    return max(counts.values()), len(counts)


def scalar_controls():
    p = 7
    cases = (
        # f=sX+tX^2: one node equation contains this affine plane.
        ("affine_plane", tuple(range(6)), 3, 4, 2, 1,
         tuple((0, s, t) for s, t in product(range(p), repeat=2))),
        ("ambient_three_space", tuple(range(6)), 3, 4, 3, 1,
         tuple(product(range(p), repeat=3))),
        ("parabola", tuple(range(6)), 3, 4, 1, 2,
         tuple((s, s*s % p, 0) for s in range(p))),
        # Graph c2=c0*c1, with c3=0: an irreducible degree-two affine surface.
        ("quadric_surface", tuple(range(7)), 4, 5, 2, 2,
         tuple((s, t, s*t % p, 0) for s, t in product(range(p), repeat=2))),
    )
    rows = []
    for name, nodes, k, a, r, degree, candidates in cases:
        maximum, centers = maximum_list_on_carrier(p, nodes, candidates, a)
        bound = degree*scalar_ratio(len(nodes), k, a, r)
        assert maximum <= bound
        rows.append({"carrier": name, "dimension": r, "degree": degree,
                     "maximum_list": maximum, "counted_centers": centers,
                     "rational_bound": str(bound), "integer_bound": int(bound)})
    return rows


def mca_plane_control():
    p, n, k, t = 17, 8, 4, 6
    nodes = poly.OMEGA
    f1, f2 = (4, 4, 1, 1), (5, 1, 6, 14)
    # Single-hole received pair from the exact antipodal fixture.
    u0 = {x: 0 for x in nodes}
    u0[2], u0[4] = 7, 15
    u1 = {x: int(x == 1) for x in nodes}
    assert poly.rank([list(f1), list(f2)]) == 2
    points = []
    for s, u in product(range(p), repeat=2):
        f = tuple((s*a+u*b) % p for a, b in zip(f1, f2))
        gamma = evaluate(f, 1, p)
        support = tuple(x for x in nodes if evaluate(f, x, p) == (u0[x]+gamma*u1[x]) % p)
        if len(support) < t:
            continue
        matrix = [[pow(x, j, p) for j in range(k)] for x in support]
        base_rank = poly.rank(matrix)
        joint = all(poly.rank([row+[word[x]] for row, x in zip(matrix, support)]) == base_rank
                    for word in (u0, u1))
        if not joint:
            points.append((gamma, f, support))
    seeds = {point[0] for point in points}
    assert seeds == {0, 9, 10}
    assert len(seeds) <= mca_ratio(n, k, t, 2)
    return {"field": p, "n": n, "k": k, "threshold": t,
            "plane_points_enumerated": p*p, "selected_seeds": sorted(seeds),
            "plane_bound": str(mca_ratio(n, k, t, 2)), "joint_support_checks": len(points)}


def production_controls():
    n = 2**30
    b = (n+2)//6
    assert n == 6*b-2
    exact = mca_ratio(n, n//2, 4*b, 2)
    assert exact == n-13+Fraction(30, b+2)
    assert int(exact) == 1073741811
    rows = []
    for name, length, k, a, budget in (
            ("grand_punctured", n-1, n//2, 4*b-1, n),
            ("companion_scalar", 262144, 131072, 181353, 274980728111395087)):
        ratio = scalar_ratio(length, k, a, 2)
        # Strict next-integer boundary: floor(D*ratio)<=budget iff D*ratio<budget+1.
        max_degree = ((budget+1)*ratio.denominator-1)//ratio.numerator
        assert int(max_degree*ratio) <= budget
        assert int((max_degree+1)*ratio) > budget
        rows.append({"profile": name, "surface_factor": str(ratio),
                     "largest_sufficient_surface_degree": max_degree,
                     "budget": budget})
    return {"conditional_mca_plane_cap": int(exact), "scalar_degree_allowances": rows}


def main():
    print(json.dumps({"status": "PASS_CARRIER_INCIDENCE_CONTROLS",
                      "scalar_controls": scalar_controls(),
                      "mca_plane": mca_plane_control(),
                      "production": production_controls(),
                      "production_carrier_constructed": False,
                      "lean_verified": False}, indent=2))


if __name__ == "__main__":
    main()
