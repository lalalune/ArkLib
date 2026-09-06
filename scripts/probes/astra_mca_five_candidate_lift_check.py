#!/usr/bin/env python3
"""Five actual punctured candidates from a fixed sixteen-coset certificate.

Dense controls check all nodes at small orders. The production cell checks
only the fixed-degree certificate and exact lifting arithmetic; its general
root-count argument is written in the accompanying note, not Lean-formalized.
"""

from itertools import combinations
import json

from astra_mca_moment_rigidity_check import P, evaluate, mul, root, subtract
from astra_mca_low_degree_saturation_check import gcd
from astra_mca_pair_basis_complete_check import divide_root, interpolate, scale
from astra_mca_split_root_rigidity_check import split_off_domain_roots


EXPECTED_ROOTS = (
    (5, 6, 7, 14, 15),
    (4, 7, 12, 13, 15),
    (3, 6, 11, 13, 14),
    (3, 4, 5, 11, 12),
)


def compose_power(poly, exponent):
    out = [0] * ((len(poly) - 1) * exponent + 1)
    for j, c in enumerate(poly):
        out[j * exponent] = c
    return tuple(out)


def owner(j):
    if j % 8 == 5:
        return 0 if j == 5 else 1
    return {3: 2, 4: 1, 6: 0, 7: 0}[j % 8]


def base_certificate(p):
    eta = root(16, p)
    zeta = eta * eta % p
    nodes = [pow(eta, j, p) for j in range(16)]
    chosen = [j for j in range(16) if j % 8 not in {0, 1, 2}]
    lines = [(pow(zeta, -i, p), 0, pow(zeta, i, p)) for i in range(4)]
    h = interpolate([nodes[j] for j in chosen],
                    [evaluate(lines[owner(j)], nodes[j], p) for j in chosen], p)
    assert len(h) == 10
    quotients, records = [], []
    for i, line in enumerate(lines):
        error = subtract(h, line, p)
        actual = tuple(j for j, x in enumerate(nodes) if evaluate(error, x, p) == 0)
        # This exact root census is asserted for the actual production prime.
        if p == P:
            assert actual == EXPECTED_ROOTS[i]
        assert tuple(j for j in actual if j in chosen) == EXPECTED_ROOTS[i]
        q = error
        for j in actual:
            q = divide_root(q, nodes[j], p)
        if p == P:
            assert len(q) == 5 and all(evaluate(q, x, p) for x in nodes)
        quotients.append(q)
        records.append({"candidate": i, "base_domain_roots": actual,
                        "outside_quotient_coefficients": q})
    for i, j in combinations(range(4), 2):
        lhs = subtract(lines[i], lines[j], p)
        rhs = scale((-pow(zeta, -(i + j), p), 0, 1),
                    (pow(zeta, i, p) - pow(zeta, j, p)) % p, p)
        assert lhs == rhs
    r = mul(mul((1, 1), (-zeta % p, 0, 1), p), (-zeta * zeta % p, 0, 1), p)
    v_base = mul(r, h, p)
    c = (1 - zeta - zeta * zeta + pow(zeta, -1, p)) % p
    fifth = mul((0, 0, c), mul((1, 1), (-zeta * zeta % p, 0, 1), p), p)
    assert c and len(fifth) == 6
    fifth_error = subtract(v_base, fifth, p)
    fifth_roots = tuple(j for j, x in enumerate(nodes) if evaluate(fifth_error, x, p) == 0)
    assert fifth_roots == (2, 3, 4, 6, 7, 8, 10, 11, 12, 14, 15)
    fifth_q = fifth_error
    for j in fifth_roots:
        fifth_q = divide_root(fifth_q, nodes[j], p)
    assert len(fifth_q) == 4 and all(evaluate(fifth_q, x, p) for x in nodes)
    # Every difference has only domain roots, so the outside factors of
    # distinct errors are coprime even over an algebraic closure.
    for i, (a, b) in enumerate(((6, 7), (4, 7), (3, 6), (3, 4))):
        diff = subtract(mul(r, lines[i], p), fifth, p)
        factored = mul(mul((1, 1), (-zeta * zeta % p, 0, 1), p),
                       mul((-pow(zeta, a, p) % p, 0, 1),
                           (-pow(zeta, b, p) % p, 0, 1), p), p)
        assert diff == scale(factored, pow(zeta, i, p), p)
    quotients.append(fifth_q)
    assert all(gcd(a, b, p) == [1] for a, b in combinations(quotients, 2))
    return {"prime": p, "eta": eta, "zeta": zeta,
            "h_coefficients": h, "lines": lines, "candidates": records,
            "fifth_constant": c, "fifth_coefficients": fifth,
            "fifth_base_domain_roots": fifth_roots,
            "fifth_outside_quotient_coefficients": fifth_q,
            "pairwise_outside_gcd_checks": 10,
            "base_points_checked_per_candidate": 16}, quotients


def parity_weights(xs, p):
    weights = []
    for i, x in enumerate(xs):
        denominator = 1
        for j, y in enumerate(xs):
            if i != j:
                denominator = denominator * (x - y) % p
        weights.append(pow(denominator, -1, p))
    return weights


def dense_control(n, p, full_list=False):
    base, quotients = base_certificate(p)
    s, d, k = n // 16, n // 8, n // 2
    g = root(n, p)
    assert n % 16 == 0 and pow(g, s, p) == base["eta"]
    zeta = base["zeta"]
    nodes = [pow(g, j, p) for j in range(n)]
    r = mul(mul((1,) * d, (-zeta % p,) + (0,) * (d - 1) + (1,), p),
            (-zeta * zeta % p,) + (0,) * (d - 1) + (1,), p)
    h_lift = compose_power(base["h_coefficients"], s)
    v_poly = mul(r, h_lift, p)
    r_base = mul(mul((1, 1), (-zeta % p, 0, 1), p),
                 (-zeta * zeta % p, 0, 1), p)
    assert r == mul((1,) * s, compose_power(r_base, s), p)
    fs = [mul(r, compose_power(line, s), p) for line in base["lines"]]
    fs.append(mul((1,) * s, compose_power(base["fifth_coefficients"], s), p))
    assert len(r) - 1 == 3 * d - 1
    assert len(v_poly) - 1 == 15 * s - 1 <= n - 2
    assert all(len(f) == k for f in fs[:4]) and len(fs[4]) == 6 * s
    v = [evaluate(v_poly, x, p) for x in nodes]
    expected_agreement = 11 * s - 1
    records = []
    for i, f in enumerate(fs):
        values = [evaluate(f, x, p) for x in nodes]
        agree = [j for j in range(1, n) if v[j] == values[j]]
        candidate_agreement = expected_agreement if i < 4 else 12 * s - 1
        assert len(agree) == candidate_agreement
        gamma = values[0]
        # On k punctured agreements plus the hole, a parity check separates
        # the direction word from every degree-less-than-k polynomial.
        short = agree[:k] + [0]
        weights = parity_weights([nodes[j] for j in short], p)
        assert len(short) == k + 1
        assert all(sum(a * pow(nodes[j], power, p) for a, j in zip(weights, short)) % p == 0
                   for power in range(k))
        syndrome0 = sum(a * (v[j] if j else 0) for a, j in zip(weights, short)) % p
        syndrome1 = weights[-1]
        assert syndrome1 and (syndrome0 + gamma * syndrome1) % p == 0
        error = subtract(v_poly, f, p)
        if p == P:
            multiplicities, outside = split_off_domain_roots(error, n, g, p)
            assert sum(multiplicities) == candidate_agreement
            assert outside == compose_power(quotients[i], s)
            assert len(outside) - 1 == (4 if i < 4 else 3) * s
        records.append({"candidate": i, "degree": len(f) - 1,
                        "punctured_agreements": len(agree), "value_at_hole": gamma,
                        "no_joint_parity_syndrome": [syndrome0, syndrome1],
                        "support_with_hole": len(agree) + 1})
    assert len({r["value_at_hole"] for r in records}) == 5
    result = {"n": n, "prime": p, "received_degree": len(v_poly) - 1,
              "candidates": records, "distinct_bad_scalars_at_least": 5,
              "outside_degrees": [4 * s] * 4 + [3 * s] if p == P else None,
              "production_domain_checked": False}
    if full_list:
        found = set()
        supports_checked = 0
        # Every qualifying polynomial contains one of these agreement supports.
        for support in combinations(range(1, n), expected_agreement):
            supports_checked += 1
            first = support[:k]
            f = interpolate([nodes[j] for j in first], [v[j] for j in first], p)
            if all(evaluate(f, nodes[j], p) == v[j] for j in support[k:]):
                found.add(f)
        assert set(fs) == found
        result["entire_finite_list_size"] = len(found)
        result["full_list_agreement_threshold"] = expected_agreement
        result["agreement_supports_enumerated"] = supports_checked
        result["entire_finite_list_coefficients"] = sorted(found)
        result["entire_finite_value_set"] = sorted({evaluate(f, 1, p) for f in found})
    return result


def production_certificate():
    base, quotients = base_certificate(P)
    n, s, d, k = 2 ** 30, 2 ** 26, 2 ** 27, 2 ** 29
    a = 715827883
    zeta = base["zeta"]
    r1 = d * (1 - zeta) * (1 - zeta * zeta) % P
    assert r1
    values = [r1 * evaluate(line, 1, P) % P for line in base["lines"]]
    values.append(s * evaluate(base["fifth_coefficients"], 1, P) % P)
    assert len(set(values)) == 5
    assert 11 * s - 1 >= a
    assert 3 * d - 1 + d == k - 1
    assert 15 * s - 1 <= n - 2
    assert 5 * 2 ** 128 < P
    return {"n": n, "prime": P, "first_four_common_root_count": 3 * d - 1,
            "candidate_degrees": [k - 1] * 4 + [6 * s - 1],
            "received_degree": 15 * s - 1,
            "punctured_agreements": [11 * s - 1] * 4 + [12 * s - 1],
            "required_predecessor_agreements": a,
            "agreement_margin": 11 * s - 1 - a,
            "outside_factor_degrees": [4 * s] * 4 + [3 * s],
            "five_values_at_hole": values,
            "five_pairwise_coprime_outside_factors_use_difference_identity": True,
            "radius_for_five_bad_scalars": "5/16",
            "five_scalars_exceed_security_budget": False,
            "fixed_base_certificate": base,
            "production_domain_enumerated": False,
            "production_polynomials_expanded": False,
            "full_list_size_claimed": False}


def main():
    result = {"status": "PASS_FIVE_CANDIDATE_LIFT_CONTROLS",
              "dense_controls": [dense_control(16, P, full_list=True),
                                 dense_control(64, P), dense_control(256, P),
                                 dense_control(64, 257), dense_control(64, 65537)],
              "production": production_certificate(),
              "production_argument_Lean_formalized": False,
              "independently_reviewed": False, "prize_solved": False}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
