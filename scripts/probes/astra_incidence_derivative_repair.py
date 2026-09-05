#!/usr/bin/env python3
"""Check derivative/contact transcription and necessary profile arithmetic.

The uniform profile is arithmetic only, not a constructed universal factor.
No C2 score change or Lean proof is asserted. Uses Python's standard library.
"""

from itertools import product
from math import factorial

P, W, N, AGREEMENT = 2130706433, 131071, 262144, 181353


def add(a, b):
    c = a.copy()
    for e, v in b.items():
        c[e] = (c.get(e, 0) + v) % P
        if c[e] == 0:
            del c[e]
    return c


def scale(a, c):
    return {e: v*c % P for e, v in a.items() if v*c % P}


def mul(a, b):
    c = {}
    for e, x in a.items():
        for f, y in b.items():
            g = tuple(u+v for u, v in zip(e, f))
            c[g] = (c.get(g, 0)+x*y) % P
    return {e: v for e, v in c.items() if v}


def power(a, n):
    b = {(0, 0, 0, 0): 1}
    for _ in range(n):
        b = mul(a, b)
    return b


def diff(a, j):
    b = {}
    for e, v in a.items():
        if e[j]:
            f = list(e)
            f[j] -= 1
            b[tuple(f)] = v*e[j] % P
    return {e: v for e, v in b.items() if v}


def variable(j):
    return {tuple(int(i == j) for i in range(4)): 1}


def contact_order(a):
    return min(e[0]+2*e[1] for e in a)


def local_identity_checks():
    t, v, r, z = [variable(j) for j in range(4)]
    one = {(0, 0, 0, 0): 1}
    substitutions = [add(t, scale(one, 5)),
                     add(add(scale(one, 2), scale(z, 3)), add(mul(r, t), v)),
                     r, z]
    checks = 0
    for exps in product(range(3), range(4), range(4), range(2)):
        localized = one
        for x, e in zip(substitutions, exps):
            localized = mul(localized, power(x, e))
        nu = contact_order(localized)
        differentiated = localized
        for h in range(4):
            expected = {}
            if h <= exps[2]:
                expected = one
                for j, (x, e) in enumerate(zip(substitutions, exps)):
                    expected = mul(expected, power(x, e-h if j == 2 else e))
                expected = scale(expected, factorial(exps[2])//factorial(exps[2]-h))
            assert differentiated == expected
            if differentiated:
                assert contact_order(differentiated) >= max(0, nu-h)
            differentiated = add(diff(differentiated, 2),
                                 scale(mul(t, diff(differentiated, 1)), -1))
            checks += 1
    return checks


def main():
    c = W*47-10
    h_cap = c-(W-1)
    assert (c, h_cap) == (6160327, 6029257)
    thresholds = [h*(W-1)+1 for h in range(1, 11)]
    assert thresholds[0] == 131071 and thresholds[-1] == 1310701

    # Check the already identified uniform profile against the strengthened
    # derivative inequalities, full repair tests, and H-agreement incidence.
    nu, total = 34, 2364
    rho = nu*(nu+1)*(total+1)//2-nu*(nu-1)*(nu+1)//6
    coefficients = sum((total+1-y)*(c+1-W*y)
                       for y in range(min(total, c//W)+1))
    assert N*nu > c and N*rho >= coefficients == 347392733438
    assert all(N*min(h, nu) >= bound for h, bound in enumerate(thresholds, 1))
    spent = AGREEMENT*(nu-1)
    assert spent == 5984649 and h_cap-spent == 44608
    assert h_cap//(nu-1) == 182704 >= AGREEMENT
    print(f"local_derivative_identity_checks: {local_identity_checks()}")
    print(f"necessary_sum_min_h_thresholds_h1_to_h10: {thresholds}")
    print(f"necessary_positive_contact_nodes_at_least: {thresholds[0]}")
    print(f"uniform_order34_H_roots: {spent}; degree_cap: {h_cap}; slack: {h_cap-spent}")
    print("PASS: necessary conditions only; uniform scalar profile survives; no C2 score change")


if __name__ == "__main__":
    main()
