#!/usr/bin/env python3
"""Four deletions and a separating projection for an analytic MCA upper bound.

Small instances reconstruct all codewords and witnesses. The production
cell checks only constant-size arithmetic; existence there is proved in
docs/kb/astra_mca_four_delete-2026-09-05.md, not by a large enumeration.
"""
import json
from math import comb

from astra_mca_paircover_four_cosets import label
from astra_mca_two_generator_probe import P, multiply, vanishing, evaluate
from astra_mca_two_generator_delete_probe import divide_linear, linear_combination, parity_weights
from astra_mca_twogen_lift_eval import RecursiveMap, interpolate_h, quotient, PRODUCTION_N


def trim(poly):
    out = [a % P for a in poly]
    while len(out) > 1 and not out[-1]:
        out.pop()
    return out or [0]


def exact_divide(poly, root):
    """Include the zero polynomial, whose quotient remains zero."""
    poly = trim(poly)
    return [0] if poly == [0] else trim(divide_linear(poly, root))


def combine(a, b, x=1, y=1):
    return trim(linear_combination(a, b, x, y))


def wedge(a, b):
    return (a[0]*b[1]-a[1]*b[0]) % P


def determinant(first, second):
    return combine(multiply(first[1], second[2]), multiply(second[1], first[2]), 1, -1)


def initial_generators(n):
    model = RecursiveMap(n)
    nodes = [pow(model.omega, e, P) for e in range(n)]
    h = interpolate_h(model, nodes)
    i, m = model.i, model.m
    ea, eb = (1+i) % P, P-2
    q = [i]+[0]*(m-1)+[1]
    p0 = [quotient(-i, 1-i)]+[0]*(m-1)+[quotient(1, 1-i)]
    q0 = [quotient(1, 1-i)]+[0]*(m-1)+[quotient(-1, 1-i)]
    fa, fb = [P-1]+[0]*(m-1)+[1], [-i % P]+[0]*(m-1)+[1]
    first = [[0], multiply(fa, combine(p0, h, 1, ea)),
             combine(multiply(fb, combine(q0, h, 1, eb)), [0], -1, 0)]
    second = [[0], combine(multiply(fa, q), [0], ea, 0),
              combine(multiply(fb, q), [0], -eb, 0)]
    first, second = [[trim(a) for a in triple] for triple in (first, second)]
    assert determinant(first, second) == [P-1]+[0]*(n-1)+[1]
    return nodes, first, second


def delete_pair(nodes, first, second, exponents):
    new = []
    directions = []
    for e in exponents:
        x = nodes[e]
        # The difference B-C is a nonzero cofactor row at AB and AC nodes.
        direction = tuple((evaluate(triple[1], x)-evaluate(triple[2], x)) % P
                          for triple in (first, second))
        assert any(direction)
        directions.append(direction)
        killed = [combine(a, b, direction[1], -direction[0])
                  for a, b in zip(first, second)]
        assert all(evaluate(poly, x) == 0 for poly in killed)
        new.append([exact_divide(poly, x) for poly in killed])
    assert wedge(*directions)
    return new[0], new[1], directions


def dot(a, b):
    return sum(x*y for x, y in zip(a, b)) % P


def moment(t):
    return [1, t % P, t*t % P, t*t*t % P]


def small_check(n):
    nodes, first, second = initial_generators(n)
    before = determinant(first, second)
    deletion_rows = []
    for pair in ((0, 1), (3, 7)):
        assert [label(e, n) for e in pair] == [0, 1]
        first, second, directions = delete_pair(nodes, first, second, pair)
        deletion_rows.append([list(row) for row in directions])
        expected = divide_linear(divide_linear(before, nodes[pair[0]]), nodes[pair[1]])
        actual = determinant(first, second)
        scalar = quotient(actual[-1], expected[-1])
        assert actual == trim([scalar*x % P for x in expected])
        before = actual
    private = {0, 1, 3, 7}
    remaining = [x for e, x in enumerate(nodes) if e not in private]
    det = determinant(first, second)
    assert det == trim([det[-1]*a % P for a in vanishing(remaining)])
    assert all(len(poly) <= n//2-1 for triple in (first, second) for poly in triple)
    q = (n-1)//3
    regions = [[e for e in range(n) if e not in private and label(e, n) == j]
               for j in range(3)]
    assert list(map(len, regions)) == [q-2, q-2, q+1]
    ab, ac, bc = regions
    cores = [sorted(ab+ac+list(private)), sorted(ab+bc), sorted(ac+bc)]
    assert list(map(len, cores)) == [2*q, 2*q-1, 2*q-1]
    # Four polynomial triples: U,V,XU,XV.
    basis = [first, second, [[0]+poly for poly in first], [[0]+poly for poly in second]]
    basis_values = [[[evaluate(poly, x) for x in nodes] for poly in triple] for triple in basis]
    slots = []
    owner_by_node = []
    for e, x in enumerate(nodes):
        owner = next(j for j in range(3) if e in cores[j])
        owner_by_node.append(owner)
        for j in range(3):
            residual = tuple((basis_values[t][owner][e]-basis_values[t][j][e]) % P
                             for t in range(4))
            if e in cores[j]:
                assert residual == (0, 0, 0, 0)
            else:
                assert any(residual[:2])
                assert residual[2:] == tuple(x*a % P for a in residual[:2])
                slots.append((j, e, residual))
    M = len(slots)
    assert M == n+4 and P > 3*comb(M, 2)
    for i, (_, e, row) in enumerate(slots):
        for _, f, other in slots[:i]:
            assert any((row[a]*other[b]-row[b]*other[a]) % P
                       for a in range(4) for b in range(a+1, 4))
            if e == f:
                assert e in private and wedge(row[:2], other[:2])
    # Bounded deterministic witnesses for the small controls. The general
    # argument uses polynomial root avoidance and does not require this search.
    t = next(t for t in range(1000) if all(dot(row, moment(t)) for _, _, row in slots))
    denominators = [dot(row, moment(t)) for _, _, row in slots]
    s = next(s for s in range(1000)
             if len({quotient(dot(row, moment(s)), denominator)
                     for (_, _, row), denominator in zip(slots, denominators)}) == M)
    f_values = [[dot([basis_values[t0][j][e] for t0 in range(4)], moment(s))
                 for e in range(n)] for j in range(3)]
    g_values = [[dot([basis_values[t0][j][e] for t0 in range(4)], moment(t))
                 for e in range(n)] for j in range(3)]
    u0 = [f_values[owner_by_node[e]][e] for e in range(n)]
    u1 = [g_values[owner_by_node[e]][e] for e in range(n)]
    target = 2*q
    assert target-1 >= n//2
    interpolation_bases = [core[:n//2] for core in cores]
    interpolation_weights = [parity_weights([nodes[e] for e in base])
                             for base in interpolation_bases]
    scalars, agreements = [], []
    for j, e, row in slots:
        gamma = -quotient(dot(row, moment(s)), dot(row, moment(t))) % P
        assert all(u0[x] == f_values[j][x] and u1[x] == g_values[j][x] for x in cores[j])
        assert (u1[e]-g_values[j][e]) % P
        count = sum((u0[x]+gamma*u1[x]-f_values[j][x]-gamma*g_values[j][x]) % P == 0
                    for x in range(n))
        assert count >= target
        # The core contributes at least k points to an exact target-size
        # support; polynomial uniqueness then forbids a joint explanation.
        support = cores[j][:target-1]+[e]
        assert len(set(support)) == target
        assert all((u0[x]+gamma*u1[x]-f_values[j][x]-gamma*g_values[j][x]) % P == 0
                   for x in support)
        # Independently use a Vandermonde parity check on k core points
        # plus the absent point: u1 alone has no degree-<k explanation.
        base, weights = interpolation_bases[j], interpolation_weights[j]
        product = 1
        for a in base:
            product = product*(nodes[e]-nodes[a]) % P
        interpolated = product*sum(quotient(weight*u1[a], nodes[e]-nodes[a])
                                   for a, weight in zip(base, weights)) % P
        assert (u1[e]-interpolated) % P
        scalars.append(gamma)
        agreements.append(count)
    assert len(set(scalars)) == M
    return {"n": n, "degree_bound_exclusive": n//2, "deleted_exponents": sorted(private),
            "new_basis_degree_max": max(len(poly)-1 for triple in (first, second) for poly in triple),
            "core_sizes": list(map(len, cores)), "slots": M, "distinct_finite_scalars": M,
            "no_joint_parity_checks": M,
            "projection_parameters_s_t": [s, t], "agreement_target": target,
            "minimum_actual_agreement": min(agreements), "deletion_rows": deletion_rows}


def production_check():
    n = PRODUCTION_N
    q, M = (n-1)//3, n+4
    assert n == 3*q+1 and (q+1)*3 == n+2
    assert 2*q-1 >= n//2
    root_avoidance_degree = 3*comb(M, 2)
    assert P > root_avoidance_degree and P > 3*M
    excess = M*2**128-P
    assert excess > 0
    return {"n": n, "field_size": P, "slots_guaranteed_by_written_argument": M,
            "root_avoidance_degree": root_avoidance_degree,
            "field_size_minus_root_bound": P-root_avoidance_degree,
            "core_sizes": [2*q, 2*q-1, 2*q-1], "agreement_target": 2*q,
            "unsafe_error_numerator": q+1, "radius_denominator": n,
            "strict_probability_budget_excess": excess,
            "full_production_polynomials_or_directions_enumerated": False,
            "production_projection_parameters_computed": False}


def main():
    print(json.dumps({"status": "PASS_FOUR_DELETION_MCA_CONTROLS",
                      "small_controls": [small_check(n) for n in (16, 64, 256)],
                      "production_arithmetic": production_check(),
                      "matching_lower_bound_proved": False,
                      "grand_prize_solved": False, "independent_review_and_Lean_complete": False},
                     sort_keys=True))


if __name__ == "__main__":
    main()
