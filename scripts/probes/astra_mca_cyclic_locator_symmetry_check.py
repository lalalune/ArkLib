#!/usr/bin/env python3
"""Exact controls for the written order-eight invariant-space exclusion."""
from collections import Counter
from itertools import combinations
import json


def char_counts(length, order=8):
    q, r = divmod(length, order)
    return [q + (j < r) for j in range(order)]


def det_integer(a):
    a = [row[:] for row in a]
    previous, sign = 1, 1
    for j in range(len(a)-1):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            sign = -sign
        pivot = a[j][j]
        for i in range(j+1, len(a)):
            for k in range(j+1, len(a)):
                numerator = a[i][k]*pivot - a[i][j]*a[j][k]
                assert numerator % previous == 0
                a[i][k] = numerator // previous
            a[i][j] = 0
        previous = pivot
    return sign*a[-1][-1]


def character_controls():
    cases = []
    for n in (16, 64, 256, 1024, 2**30):
        b = (n+2)//6
        assert n == 6*b-2 and n % 8 == 0 and b % 2 == 1
        chars = [0, b % 8, (2*b) % 8]
        assert len(set(chars)) == 3
        source = char_counts(b)
        target = char_counts(3*b)
        convolution = [sum(source[(j-c) % 8] for c in chars) for j in range(8)]
        assert convolution == target
        matrix = [[source[(i-j) % 8] for j in range(8)] for i in range(8)]
        determinant = det_integer(matrix)
        assert determinant == b
        assert n//4 < 2*b and 13*b-2 < 16*b and (2*b) % 8 != 0
        cases.append(dict(n=n, b=b, eigencharacters=chars,
                          character_convolution_determinant=determinant,
                          all_three_root_bound=n//4,
                          adjacent_root_bound_numerator=13*b-2,
                          adjacent_root_bound_denominator=8,
                          required_roots=2*b))
    return cases


def trim(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def add(a, b, p, scale=1):
    return trim([(a[i] if i < len(a) else 0) + scale*(b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))], p)


def mul(a, b, p):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c, p)


def ev(a, x, p):
    value = 0
    for c in reversed(a):
        value = (value*x+c) % p
    return value


def gcd(a, b, p):
    while b != [0]:
        r = a[:]
        while r != [0] and len(r) >= len(b):
            j = len(r)-len(b)
            scale = r[-1]*pow(b[-1], -1, p) % p
            r = add(r, [0]*j+b, p, -scale)
        a, b = b, r
    return trim([x*pow(a[-1], -1, p) for x in a], p)


def rank(a, p):
    a = [[x % p for x in row] for row in a]
    r = 0
    for j in range(len(a[0])):
        i = next((i for i in range(r, len(a)) if a[i][j]), None)
        if i is None:
            continue
        a[r], a[i] = a[i], a[r]
        inv = pow(a[r][j], -1, p)
        a[r] = [x*inv % p for x in a[r]]
        for i in range(r+1, len(a)):
            scale = a[i][j]
            a[i] = [(x-scale*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def balance_rank(w, b, p):
    columns = [[0]*j+a for a in w for j in range(b)]
    matrix = [[a[i] if i < len(a) else 0 for a in columns] for i in range(3*b)]
    return rank(matrix, p)


def polynomial_controls(n):
    p, b = 257, (n+2)//6
    generator = pow(3, 256//n, p)
    xs = [pow(generator, j, p) for j in range(n)]
    assert len(set(xs)) == n and pow(generator, n//2, p) == p-1
    if n == 16:
        w = [[1], [0]*b+[1], [0]*(2*b)+[1]]
    else:
        assert n == 64 and b == 11
        roots8 = [pow(generator, 8*j, p) for j in range(4)]
        factors = [[-a % p]+[0]*7+[1] for a in roots8]
        f, g, h, ell = [0]*3+factors[0], factors[1], [0]*3+factors[2], factors[3]
        # Cross product of B=(f,g,0), C=(0,h,ell).
        w = [mul(g, ell, p), trim([-v for v in mul(f, ell, p)], p), mul(f, h, p)]
    assert gcd(gcd(w[0], w[1], p), w[2], p) == [1]
    assert balance_rank(w, b, p) == 3*b
    assert all(len(gcd(w[i], w[j], p))-1 <= b for i, j in combinations(range(3), 2))
    for j, a in enumerate(w):
        assert all(i % 8 == (j*b) % 8 for i, c in enumerate(a) if c)
    assert len(w[2])-1 == 2*b and w[2][-1] == 1
    assert all(len(a)-1 < 2*b for a in w[:2])
    values = [tuple(ev(a, x, p) for a in w) for x in xs]
    histogram = Counter()
    for c0 in range(p):
        for c1 in range(p):
            count = sum((c0*a+c1*v+c) % p == 0 for a, v, c in values)
            if c0 and c1:
                assert count <= n//4
            elif c1:
                assert 8*count <= 13*b-2
            elif not c0:
                assert count % 8 == 0
            # The specific controls have no qualifying locators at all.
            assert count < 2*b
            histogram[count] += 1
    assert sum(histogram.values()) == p*p
    return dict(field=p, n=n, b=b, basis=w, balance_rank=3*b,
                normalized_monic_combinations=p*p, root_count_histogram=dict(sorted(histogram.items())),
                degree_2b_domain_divisors=0)


def boundary_control():
    p, n, b = 17, 4, 1
    zeta = 2
    assert pow(zeta, 8, p) == 1 and pow(zeta, 4, p) != 1
    xs = [pow(4, j, p) for j in range(4)]
    locators = [mul([-x, 1], [-y, 1], p) for x, y in combinations(xs, 2)]
    assert len(locators) == 6 and rank(locators, p) == 3
    assert balance_rank([[1], [0, 1], [0, 0, 1]], b, p) == 3
    assert any(zeta*x % p not in xs for x in xs)
    return dict(field=p, n=n, b=b, locator_count=6, span_rank=3,
                domain_stable_under_order8=False)


if __name__ == '__main__':
    print(json.dumps(dict(status='PASS_CYCLIC_LOCATOR_SYMMETRY_CONTROLS',
                         character_controls=character_controls(),
                         polynomial_controls=[polynomial_controls(n) for n in (16, 64)],
                         essential_boundary=boundary_control(),
                         scope='Written symmetry exclusion; no universal production bound or Lean proof.'), indent=2))
