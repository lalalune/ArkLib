#!/usr/bin/env python3
"""Far-word contact-space obstruction and three exact order-two controls.

See docs/kb/astra_far_word_kernel-2026-09-05.md. No protocol claim.
"""
import json
from math import comb, isqrt

from astra_colon_audit import direct_contact_matrix, matrix_rank


def add(a, b, p):
    return [((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)) % p
            for i in range(max(len(a), len(b)))]


def scale(a, c, p):
    return [x*c % p for x in a]


def mul(a, b, p):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % p
    return c


def derivative(a, p):
    return [i*a[i] % p for i in range(1, len(a))]


def evaluate(a, x, p):
    result = 0
    for coefficient in reversed(a):
        result = (result*x+coefficient) % p
    return result


def basis(k):
    return [0]*k+[1]


def hermite(A, U, n, p):
    # deg A<=n and deg U<n imply every final term has degree <2n.
    product = mul(A, mul(derivative(U, p), [0, pow(n, -1, p)], p), p)
    remainder = [0]*n
    for degree, coefficient in enumerate(product):
        remainder[degree % n] = (remainder[degree % n]+coefficient) % p
    V = [-1]+[0]*(n-1)+[1]
    H = add(scale(mul(A, U, p), -1, p), mul(V, remainder, p), p)
    return H+[0]*(2*n-len(H))


def transpose(columns):
    return [list(row) for row in zip(*columns)]


def interpolate(nodes, values, p):
    result = [0]
    for i, (x, value) in enumerate(zip(nodes, values)):
        numerator, denominator = [1], 1
        for j, y in enumerate(nodes):
            if i != j:
                numerator = mul(numerator, [-y, 1], p)
                denominator = denominator*(x-y) % p
        result = add(result, scale(numerator, value*pow(denominator, -1, p), p), p)
    return result


def local_phi_power(prime, node, pole, multiplicity):
    L = (node-pole) % prime
    local = {(1, 0, 0): pow(L, -1, prime), (1, 0, 1): L,
             (2, 0, 1): 1, (0, 1, 0): L, (1, 1, 0): 1}
    power = {(0, 0, 0): 1}
    for _ in range(multiplicity):
        result = {}
        for first, a in power.items():
            for second, b in local.items():
                exponent = tuple(x+y for x, y in zip(first, second))
                result[exponent] = (result.get(exponent, 0)+a*b) % prime
        power = {exponent: coefficient for exponent, coefficient in result.items()
                 if coefficient}
    assert min(t+2*v for t, v, r in power) == multiplicity
    assert power[(multiplicity, 0, 0)] == pow(L, -multiplicity, prime)


def local_rank_two_phi_power(prime, node, multiplicity):
    inverse = pow(node, -1, prime)
    local = {(1, 0, 0, 0): 1, (1, 0, 0, 1): 2*inverse % prime,
             (1, 0, 1, 0): node**2 % prime, (2, 0, 0, 0): inverse,
             (2, 0, 0, 1): inverse**2 % prime, (2, 0, 1, 0): 2*node % prime,
             (3, 0, 1, 0): 1, (0, 1, 0, 0): node**2 % prime,
             (1, 1, 0, 0): 2*node % prime, (2, 1, 0, 0): 1}
    power = {(0, 0, 0, 0): 1}
    for _ in range(multiplicity):
        result = {}
        for first, a in power.items():
            for second, b in local.items():
                exponent = tuple(x+y for x, y in zip(first, second))
                result[exponent] = (result.get(exponent, 0)+a*b) % prime
        power = {exponent: coefficient for exponent, coefficient in result.items()
                 if coefficient}
    assert min(t+2*v for t, v, r, z in power) == multiplicity
    assert power[(multiplicity, 0, multiplicity, 0)] == pow(node, 2*multiplicity, prime)


def production_obstruction():
    prime, n, w = 2130706433, 262144, 131071
    D, T, Y, S, source_lower = 23944271, 4795, 182, 41, 228451639
    assert all(prime % divisor for divisor in range(2, isqrt(prime)+1))
    assert (prime-1) == 8128*n
    # The production selected-polynomial convention is degree <=w.
    assert n-w-2 == 131071 > 80791
    assert w+2 < 181353
    rows = []
    for multiplicity, expected_dimension in ((166, 10121888390), (132, 30981249640)):
        x_width, z_width = D-multiplicity*(w+2), T+1-multiplicity
        assert x_width > 0 and z_width > 0 and multiplicity <= Y
        assert S >= 0
        terms = 0
        # Phi=X^2*Y-X-Z. Check every term at the maximum permitted shifts.
        for y in range(multiplicity+1):
            for z in range(multiplicity-y+1):
                coefficient = (comb(multiplicity, y)*comb(multiplicity-y, z)
                               *(-1)**(multiplicity-y)) % prime
                if coefficient:
                    shifted_x = multiplicity+y-z+x_width-1
                    shifted_z = z+z_width-1
                    assert shifted_x+w*y < D
                    assert y+shifted_z <= T
                    assert y <= Y
                    terms += 1
        assert x_width*z_width == expected_dimension > source_lower
        rows.append({"retained_order": multiplicity, "x_width": x_width,
                     "z_width": z_width, "subspace_dimension": expected_dimension,
                     "dimension_minus_source": expected_dimension-source_lower,
                     "power_support_terms_checked": terms})
    return {"prime": prime, "companion_extension_degree": 6,
            "n": n, "line_word_distance_lower": n-w-2,
            "source_nullity_lower": source_lower, "rows": rows}


def main():
    p = 17
    rows = []
    for n, generator, w, pole in ((8, 2, 3, 0), (8, 2, 3, 3), (4, 4, 1, 0)):
        nodes = tuple(pow(generator, i, p) for i in range(n))
        assert len(set(nodes)) == n and all(pow(x, n, p) == 1 for x in nodes)
        assert pow(pole, n, p) != 1
        values = tuple(pow((x-pole) % p, -1, p) for x in nodes)
        for node in nodes:
            for multiplicity in (1, 2, 3):
                local_phi_power(p, node, pole, multiplicity)
                if pole == 0:
                    local_rank_two_phi_power(p, node, multiplicity)
        rs_and_received = [list(pow(x, k, p) for k in range(w+1))
                           +[pow(x, -1, p), pow(x, -2, p)] for x in nodes]
        assert matrix_rank(rs_and_received, p) == w+3
        D = n+w+1
        columns, matrix = direct_contact_matrix(
            p, D, 1, 1, 1, nodes, (2,)*n, values, (0,)*n, w)
        nullity = columns-matrix_rank(matrix, p)
        assert nullity == 1

        inverse = pow((pow(pole, n, p)-1) % p, -1, p)
        U = [-pow(pole, n-1-k, p)*inverse % p for k in range(n)]
        for x, value in zip(nodes, values):
            assert evaluate(U, x, p) == value
        images = [hermite(basis(k), U, n, p) for k in range(n+1)]
        for k, H in enumerate(images):
            A = basis(k)
            for x, value in zip(nodes, values):
                assert (evaluate(H, x, p)+evaluate(A, x, p)*value) % p == 0
                assert (evaluate(derivative(H, p), x, p)
                        +evaluate(derivative(A, p), x, p)*value) % p == 0
        full_rank = matrix_rank(transpose([H[D:] for H in images]), p)
        assert full_rank == n-w-1

        V = [-1]+[0]*(n-1)+[1]
        compatible = (V, basis(0), basis(n-1))
        compatible_rank = matrix_rank(
            transpose([hermite(A, U, n, p)[D:] for A in compatible]), p)
        assert compatible_rank == 2

        L = [-pole, 1]
        Vprime = derivative(V, p)
        A = add(V, scale(mul(L, Vprime, p), -1, p), p)
        B = mul(L, V, p)
        C = Vprime
        assert len(A)-1 <= n and len(B)-1 <= n+1 and len(C)-1 <= n+w
        for x, value in zip(nodes, values):
            assert evaluate(B, x, p) == 0
            assert (evaluate(A, x, p)+evaluate(derivative(B, p), x, p)) % p == 0
            assert (evaluate(C, x, p)+evaluate(A, x, p)*value) % p == 0
            assert (evaluate(derivative(C, p), x, p)
                    +evaluate(derivative(A, p), x, p)*value) % p == 0
        assert all(coefficient == 0 for coefficient in hermite(A, U, n, p)[D:])

        interpolant = interpolate(nodes[:w], values[:w], p)
        agreements = sum(evaluate(interpolant, x, p) == value
                         for x, value in zip(nodes, values))
        assert agreements == w
        rows.append({"prime": p, "n": n, "w": w, "pole": pole, "D": D,
                     "exact_distance": n-w, "full_contact_nullity": nullity,
                     "full_tail_rank": full_rank,
                     "compatible_tail_rank": compatible_rank})
    print(json.dumps({"status": "PASS_FAR_WORD_QUOTIENT_OBSTRUCTION_NO_PROTOCOL_CLAIM",
                      "production_obstruction": production_obstruction(),
                      "local_power_expansions": {"simple_pole": 60, "rank_two_line": 36},
                      "fixed_examples": rows}, indent=2))


if __name__ == "__main__":
    main()
