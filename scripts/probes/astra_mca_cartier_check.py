#!/usr/bin/env python3
"""Bounded exact Cartier-identity controls; no production exclusion."""

import json
from math import comb

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478


def trim(f):
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def add(f, g, p, scale=1):
    out = [0] * max(len(f), len(g))
    for j, value in enumerate(f):
        out[j] = value
    for j, value in enumerate(g):
        out[j] = (out[j] + scale * value) % p
    return trim(out)


def mul(f, g, p):
    out = [0] * (len(f) + len(g) - 1)
    for j, a in enumerate(f):
        for k, b in enumerate(g):
            out[j + k] = (out[j + k] + a * b) % p
    return trim(out)


def power(f, exponent, p):
    out = [1]
    for _ in range(exponent):
        out = mul(out, f, p)
    return out


def derivative(f, p):
    return trim([j * f[j] % p for j in range(1, len(f))] or [0])


def primitive_control(p):
    k = (p - 2) // 3
    assert p == 3 * k + 2
    a, b = [1, 1, 1], [2, 0, 1]
    h = mul(mul(a, b, p), add(a, b, p), p)
    w = add(mul(derivative(a, p), b, p), mul(a, derivative(b, p), p), p, -1)
    primitive = [0]
    for j in range(k + 1):
        exponent = k + j + 1
        assert 0 < exponent < p and p - exponent >= k + 1
        term = mul(power(a, exponent, p), power(b, p - exponent, p), p)
        primitive = add(primitive, term, p, comb(k, j) * pow(exponent, -1, p))
    target = mul(w, power(h, k, p), p)
    assert derivative(primitive, p) == target
    assert all(target[j] == 0 for j in range(p - 1, len(target), p))


def main():
    for p in (5, 11, 17):
        primitive_control(p)
    n = 2**30
    i = pow(G, n // 4, P)
    assert i * i % P == P - 1
    a = [-i % P, 0, 0, 0, 1]
    b = [(i - 1) % P, 0, 0, 0, (i - 1) % P]
    c = [-1 % P, 0, 0, 0, i]
    d = [-1 % P, 0, 0, 0, 1]
    assert add(a, b, P) == c
    h = mul(mul(a, b, P), c, P)
    scale = -(1 + i) % P
    assert h == [scale if j % 4 == 0 else 0 for j in range(13)]
    assert mul(d, h, P) == [(-scale) % P] + [0] * 15 + [scale]
    w = add(mul(derivative(a, P), b, P), mul(a, derivative(b, P), P), P, -1)
    assert w == [0, 0, 0, P - 8]
    # At length16, the output indices are 0,1,2, but residues require3 mod4.
    assert P % 4 == 1 and all(j % 4 != 3 for j in range(3))
    m, L, k = (n - 4) // 3, (P - 1) // n, (P - 2) // 3
    assert n == 3 * m + 4 and P == 3 * k + 2 == n * L + 1
    assert 2 * m - 2 < n
    assert (n * k + 2 * m - 2 - (P - 1)) // P == m
    assert L * (m + 1) <= k < L * (m + 2)
    assert (3 * m * k + 2 * m - 2 - (P - 1)) // P == m - 2
    assert (2 * m - 1) - (m - 1) == m
    print(json.dumps(dict(
        status='PASS_CARTIER_IDENTITY_AND_QUARTIC_DEFECT_CONTROL',
        primitive_identity_fields=[5, 11, 17], actual_prime_control_length=16,
        control_wronskian_order=3, production_m=m,
        actual_operator_kernel_dimension_lower=m,
        undeleted_diagonal_last_index=m,
        production_exclusion=False, lean_formalized=False
    ), sort_keys=True))


if __name__ == '__main__':
    main()
