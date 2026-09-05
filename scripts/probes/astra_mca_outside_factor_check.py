#!/usr/bin/env python3
"""Outside-factor controls: a complete small line census and a production example.

Neither check bounds arbitrary production lists. Production polynomial
identities are proved in the accompanying note; only eight possible domain
roots of its two outside factors need explicit field checks.
"""
from collections import Counter, defaultdict
from itertools import combinations
import json

from astra_mca_moment_rigidity_check import P, G, evaluate, locator, mul, root, subtract
from astra_mca_split_root_rigidity_check import split_off_domain_roots


def scale(poly, scalar, p):
    return tuple(c*scalar % p for c in poly)


def line_census(p):
    n, k, A, degree = 16, 8, 11, 12
    z = root(n, p)
    nodes = {pow(z, i, p) for i in range(n)}
    lines = []
    for support in combinations(range(1, n), A):
        H = locator(support, z, p)
        first = H[A-1]
        slope = H[k:A]
        intercept = tuple((H[j-1]-first*H[j]) % p for j in range(k, A))
        lines.append((support, H, slope, intercept, first))
    points = defaultdict(set)
    intersections, parallel = 0, 0
    for i, (_, _, slope, intercept, _) in enumerate(lines):
        for j in range(i):
            _, _, slope1, intercept1, _ = lines[j]
            d = tuple((x-y) % p for x, y in zip(slope, slope1))
            a = tuple((y-x) % p for x, y in zip(intercept, intercept1))
            pivot = next((l for l, value in enumerate(d) if value), None)
            if pivot is None:
                # Coincident lines would force two degree-11 locators to
                # differ in degree <=6 despite at least seven common roots.
                assert any(a)
                parallel += 1
                continue
            if any((a[l]*d[pivot]-a[pivot]*d[l]) % p for l in range(len(d))):
                continue
            w = a[pivot]*pow(d[pivot], -1, p) % p
            point = tuple((intercept[l]+w*slope[l]) % p for l in range(len(d)))+(w,)
            points[point].update((i, j))
            intersections += 1
    histogram, outside_histogram = Counter(), Counter()
    max_example, max_outside_example = None, None
    for point, ids in points.items():
        polynomials = {}
        for idx in ids:
            support, H, _, _, first = lines[idx]
            beta = (first-point[-1]) % p
            error = mul(H, (-beta % p, 1), p)
            assert error[k:degree] == point
            polynomials[error] = {"support": support, "extra_root": beta,
                                  "extra_root_outside_domain": beta not in nodes}
        V = next(iter(polynomials))
        values = []
        for error, record in polynomials.items():
            f = subtract(V, error, p)
            assert len(f) <= k
            assert all(evaluate(error, pow(z, i, p), p) == 0 for i in record['support'])
            values.append(evaluate(f, 1, p))
        assert len(set(values)) == len(polynomials)
        count = len(polynomials)
        outside_count = sum(record['extra_root_outside_domain'] for record in polynomials.values())
        histogram[count] += 1
        outside_histogram[outside_count] += 1
        example = {"received_top_coefficients": point, "candidate_records": list(polynomials.values()),
                   "outside_candidates": outside_count}
        if max_example is None or count > len(max_example['candidate_records']):
            max_example = example
        if max_outside_example is None or outside_count > max_outside_example['outside_candidates']:
            max_outside_example = example
    if p == P:
        assert intersections == 30030 and len(points) == 455
        assert histogram == {1: 455} and outside_histogram == {0: 455}
    return {"n": n, "prime": p, "received_degree": degree, "agreement_threshold": A,
            "lines": len(lines), "all_line_pairs": len(lines)*(len(lines)-1)//2,
            "parallel_pairs": parallel, "intersecting_pairs": intersections,
            "intersection_points": len(points),
            "distinct_polynomial_histogram_at_intersections": dict(sorted(histogram.items())),
            "outside_candidate_histogram_at_intersections": dict(sorted(outside_histogram.items())),
            "whole_list_maximum": max(1, max(histogram)),
            "outside_sublist_maximum": max(1, max(outside_histogram)),
            "largest_list_example": max_example,
            "largest_outside_sublist_example": max_outside_example,
            "arbitrary_field_points_enumerated": False}


def root_candidate_certificate(n):
    p, z, ell = P, root(n, P), n//4
    r, s = z, z*z % p
    u, w, v = pow(r, ell, p), pow(s, ell, p), pow(z, 3*ell, p)
    alpha, beta, gamma = (v-w) % p, (s-r) % p, (v-u) % p
    assert all((alpha, beta, gamma))
    checks = []
    for t in (s, r):
        t_power = pow(t, ell, p)
        rows = []
        for j in range(4):
            coset_value = pow(z, j*ell, p)
            x = (t-beta*(coset_value-t_power)*pow(alpha, -1, p)) % p
            in_coset = pow(x, ell, p) == coset_value
            numerator = ((alpha+beta*ell*pow(t, ell-1, p)) % p if x == t else
                         (alpha+beta*(pow(x, ell, p)-t_power)*pow((x-t) % p, -1, p)) % p)
            is_root = in_coset and numerator == 0
            assert not is_root
            rows.append({"coset": j, "only_possible_root": x,
                         "lies_in_this_coset": in_coset,
                         "polynomial_numerator_zero": numerator == 0})
        checks.append({"geometric_base": t, "four_exhaustive_candidates": rows,
                       "domain_root_count": 0})
    return {"n": n, "prime": p, "r": r, "s": s, "u": u, "w": w, "v": v,
            "alpha": alpha, "beta": beta, "gamma": gamma,
            "root_candidate_checks": checks}


def small_pair_construction(n):
    p, z, ell = P, root(n, P), n//4
    k, b = n//2, (n+2)//6
    A, common_degree = k+b, ell+b
    c = root_candidate_certificate(n)
    r, s = c['r'], c['s']
    alpha, beta, gamma = c['alpha'], c['beta'], c['gamma']
    Gr = tuple(pow(r, ell-1-j, p) for j in range(ell))
    Gs = tuple(pow(s, ell-1-j, p) for j in range(ell))

    def inverse_piece(Gt):
        numerator = list(scale(Gt, beta, p))
        numerator[0] = (numerator[0]+alpha) % p
        return scale(numerator, pow(alpha*gamma % p, -1, p), p)

    Q, Q1 = inverse_piece(Gs), inverse_piece(Gr)
    FU = mul(Gr, (-s % p, 1), p)
    FW = (-c['v'] % p,)+(0,)*(ell-1)+(1,)
    assert subtract(mul(FU, Q, p), mul(FW, Q1, p), p) == (1,)
    U = {i for i in range(n) if i % 4 == 1 and i != 1} | {2}
    W = {i for i in range(n) if i % 4 == 3}
    common = [i for i in range(1, n) if i not in U | W][:common_degree]
    assert len(U) == len(W) == ell and U.isdisjoint(W) and len(common) == common_degree
    R = locator(common, z, p)
    V = mul(R, mul(FU, Q, p), p)
    other_error = mul(R, mul(FW, Q1, p), p)
    assert subtract(V, other_error, p) == R
    assert len(V)-1 == b+3*ell-1 <= n-2 and len(R) <= k
    assert evaluate(R, 1, p) != 0
    outside_parts, agreements = [], []
    for error, Qpart in ((V, Q), (other_error, Q1)):
        counts, remaining = split_off_domain_roots(error, n, z, p)
        assert remaining == Qpart
        assert sum(counts) == A and sum(counts[i] > 0 for i in range(1, n)) == A
        assert counts[0] == 0
        agreements.append(A)
        outside_parts.append(scale(remaining, pow(remaining[-1], -1, p), p))
    assert outside_parts[0] != outside_parts[1] and len(Q) == len(Q1) == ell
    return {"n": n, "prime": p, "received_degree": len(V)-1,
            "nonzero_candidate_degree": len(R)-1, "candidate_count_at_least": 2,
            "punctured_agreements": agreements, "distinct_values_at_hole": 2,
            "outside_degrees": [len(part)-1 for part in outside_parts],
            "outside_factors_distinct": True, "Bezout_identity_checked_as_polynomials": True,
            "full_list_size_claimed": False}


def production_pair():
    n = 2**30
    k, b, ell = n//2, (n+2)//6, n//4
    c = root_candidate_certificate(n)
    assert P == n*(2**128+192)+1 and pow(G, n, P) == 1 and pow(G, n//2, P) != 1
    assert b+1 <= ell-1
    assert ell+b < k and b+3*ell-1 <= n-2
    assert (ell-1)+(b+1) == ell+b
    return {**c, "received_degree": b+3*ell-1, "nonzero_candidate_degree": ell+b,
            "punctured_agreement_each": k+b, "outside_degree_each": ell-1,
            "different_coprime_outside_factors_use_written_Bezout_identity": True,
            "full_list_size_claimed": False, "over_budget_counterexample": False,
            "production_polynomials_expanded": False, "production_domain_enumerated": False}


def main():
    result = {"status": "PASS_OUTSIDE_FACTOR_CONTROLS",
              "complete_one_extra_root_line_census": [line_census(p) for p in (17, 97, 1153, P)],
              "small_pair_constructions": [small_pair_construction(n) for n in (16, 64, 256)],
              "production_pair": production_pair(),
              "Lean_formalization": False, "independent_mathematical_review": False,
              "production_outside_factor_count_bound": False, "prize_solved": False}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
