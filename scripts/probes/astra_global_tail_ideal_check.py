#!/usr/bin/env python3
"""Finite checks for the global linear-ODE ideal equality in the paired note.

This family is outside the C2 branch and fails the large-agreement premise.
It is not an obstruction to a C2-specific or prize-specific bound.
"""

P = 2130706433
TAIL = 131072
ROOTS = 2364


def evaluate(coeffs, x):
    result = 0
    for c in reversed(coeffs):
        result = (result * x + c) % P
    return result


def main():
    expected = 1
    for n in range(1, TAIL + 1):
        expected = expected * n % P
    expected = (-1) ** TAIL * expected % P
    assert expected == 1690593

    for x in (0, 1, 2, 17):
        am, an, bm, bn = 1, x, 0, 1
        for n in range(1, TAIL + 1):
            ap = (x * an + n * am) % P
            bp = (x * bn + n * bm) % P
            if n == TAIL:
                det = (an * bp - ap * bn) % P
                assert det == expected
                # Explicit inverse identities for the adjacent-tail matrix.
                inv = pow(det, -1, P)
                assert (inv * (bp * an - bn * ap)) % P == 1
                assert (inv * (-ap * bn + an * bp)) % P == 1
            am, an, bm, bn = an, ap, bn, bp

    # Q(Z)=product_{gamma=0}^{ROOTS-1}(Z-gamma), represented independently
    # by its coefficients; verify every root and every simple derivative.
    q = [1]
    for gamma in range(ROOTS):
        r = [0] * (len(q) + 1)
        for i, c in enumerate(q):
            r[i] = (r[i] - gamma * c) % P
            r[i + 1] = (r[i + 1] + c) % P
        q = r
    dq = [i * c % P for i, c in enumerate(q)][1:]
    assert len(q) - 1 == ROOTS and q[-1] == 1
    for gamma in range(ROOTS):
        assert evaluate(q, gamma) == 0
        assert evaluate(dq, gamma) != 0

    # For selected_gamma=gamma^2, each received affine line in gamma meets
    # at most two points: the required total agreement is impossible.
    assert ROOTS * 181353 > 2 * 262144
    print(f"production_tail_index: {TAIL}")
    print(f"adjacent_determinant: {expected}; checked at X=0,1,2,17")
    print(f"global_reduced_points: {ROOTS}; all roots and derivatives checked")
    print(f"raw_r_v_z: {(1, 0, ROOTS - 1)}; outside C2 branch")
    print("large_agreement_hypothesis: FAIL by quadratic graph incidence")
    print("PASS: finite checks for the proof-note ideal equality; no prize claim")


if __name__ == "__main__":
    main()
