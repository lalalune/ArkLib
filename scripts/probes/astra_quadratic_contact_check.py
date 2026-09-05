#!/usr/bin/env python3
"""Exact controls for the full quadratic contact obstruction; not a prize proof."""
import json
from math import comb

from astra_mca_moment_rigidity_check import P, evaluate, mul, root, subtract
from astra_riccati_contact_check import add, derivative, kernel, trim

PAIRS = ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (0, 2))


def scale(f, scalar, p):
    return trim(scalar * a % p for a in f)


def hasse(f, x, j, p):
    return sum(comb(i, j) * f[i] * pow(x, i-j, p) for i in range(j, len(f))) % p


def verify_contact(coefficients, nodes, values, p, m):
    """Check the six collected coefficients, independently of matrix elimination."""
    a, b, c, d, e, f = coefficients
    count = 0
    for x, v in zip(nodes, values):
        t = (-x % p, 1)
        z = add(b, scale(c, 2*v, p), p)
        local = (
            (add(add(a, scale(b, v, p), p), scale(c, v*v, p), p), m),
            (add(add(d, scale(e, v, p), p), mul(t, z, p), p), m),
            (add(add(f, mul(t, e, p), p), mul(mul(t, t, p), c, p), p), m),
            (z, max(0, m-2)),
            (add(e, scale(mul(t, c, p), 2, p), p), max(0, m-2)),
            (c, max(0, m-4)),
        )
        for polynomial, order in local:
            for j in range(order):
                assert hasse(polynomial, x, j, p) == 0
                count += 1
    return count


def three_candidate_control(n, p, g):
    # Check the exact order, including odd prime factors for n=20.
    assert pow(g, n, p) == 1
    for q in range(1, n):
        assert pow(g, q, p) != 1
    N = n+1
    assert (N+3) % 6 == 0
    b = (N+3)//6
    w, A, ell = 3*b-2, 4*b-1, n//4
    fourth = pow(g, ell, p)
    U = [(-pow(fourth, j, p) % p,)+(0,)*(ell-1)+(1,) for j in range(4)]
    V = mul(U[0], mul(U[1], U[2], p), p)
    candidates = [(0,), subtract(V, mul(U[0], mul(U[1], U[3], p), p), p),
                  subtract(V, mul(U[0], mul(U[2], U[3], p), p), p)]
    assert len(set(candidates)) == 3
    nodes = [pow(g, j, p) for j in range(n)]+[0]
    assert len(set(nodes)) == N
    values = [evaluate(V, x, p) for x in nodes]
    agreements = []
    for candidate in candidates:
        assert len(candidate)-1 <= w
        count = sum(evaluate(candidate, x, p) == v for x, v in zip(nodes, values))
        assert count >= A
        agreements.append(count)
    profiles = []
    for m in range(1, 5):
        columns, rank, nulls = kernel(nodes, values, p, w, A, m, PAIRS)
        assert rank == columns and not nulls
        profiles.append({"contact_order": m, "columns": columns, "rank": rank, "nullity": 0})
    if n == 20:
        assert [row['columns'] for row in profiles] == [26, 104, 194, 284]
    return {"field": p, "b": b, "domain": "mu_%d union zero" % n, "N": N, "w": w,
            "A": A, "candidate_agreements": agreements, "profiles": profiles}


def exceptional_order_three_control():
    # For v=0, Q=-Z' Y^2+Z YR is a nonzero contact source at m=3.
    # Thus eliminating YR at m=3 really needs the multiple-candidate argument.
    p, N, w, A, m = 101, 21, 10, 15, 3
    nodes = list(range(N))
    Z = (1,)
    for x in nodes:
        Z = mul(Z, (-x % p, 1), p)
    coefficients = ((0,), (0,), scale(derivative(Z, p), -1, p), (0,), Z, (0,))
    for polynomial, (i, j) in zip(coefficients, PAIRS):
        if polynomial != (0,):
            assert len(polynomial)-1+w*i+(w-1)*j < m*A
    count = verify_contact(coefficients, nodes, [0]*N, p, m)
    assert coefficients[4] != (0,)
    return {"field": p, "N": N, "w": w, "A": A, "contact_order": m,
            "source": "-Z'(X) Y^2 + Z(X) YR", "received_word": "zero",
            "nonzero_YR_coefficient": True, "weighted_degree": N+2*w-1,
            "cap": m*A, "collected_contact_conditions_checked": count,
            "two_candidate_hypothesis_cannot_be_dropped": True}


def arithmetic_controls():
    count = 0
    for b in range(4, 25):
        N, w, A = 6*b-3, 3*b-2, 4*b-1
        for m in range(1, 25):
            qF = min(m, 1+max(0, m-2), 2+max(0, m-4))
            qE = 1 if m == 2 else max(0, m-2)
            assert N*qF+2*(w-1) >= m*A
            if m != 3:
                assert N*qE+2*w-1 >= m*A
            else:
                # D+fE has N simple roots and at least A additional roots.
                assert N+A > 3*A-w
            count += 1
    return {"integer_profiles_checked": count, "production_all_m_has_separate_Lean_proof": True}


def main():
    controls = [three_candidate_control(20, 101, 32),
                three_candidate_control(32, P, root(32, P))]
    print(json.dumps({"status": "PASS_FULL_QUADRATIC_CONTACT_CONTROLS",
                      "three_candidate_controls": controls,
                      "order_three_exception": exceptional_order_three_control(),
                      "arithmetic": arithmetic_controls(),
                      "finite_control_is_production_size": False,
                      "prize_solved": False}, indent=2))


if __name__ == '__main__':
    main()
