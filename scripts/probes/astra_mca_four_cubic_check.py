#!/usr/bin/env python3
"""Exact production-prime certificate; standard library only."""
from collections import defaultdict
from fractions import Fraction
import json
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2 ** 30

def trim(f):
    f = [a % P for a in f]
    while len(f) > 1 and (not f[-1]):
        f.pop()
    return f

def sub(f, g):
    return trim([(f[i] if i < len(f) else 0) - (g[i] if i < len(g) else 0) for i in range(max(len(f), len(g)))])

def mul(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i + j] = (h[i + j] + a * b) % P
    return trim(h)

def ev(f, x):
    h = 0
    for a in reversed(f):
        h = (h * x + a) % P
    return h

def divmodp(f, g):
    f = trim(f)
    q = [0] * max(1, len(f) - len(g) + 1)
    iv = pow(g[-1], -1, P)
    while f != [0] and len(f) >= len(g):
        j = len(f) - len(g)
        a = f[-1] * iv % P
        q[j] = a
        f = sub(f, [0] * j + [a * b for b in g])
    return (trim(q), f)

def gcdp(f, g):
    while g != [0]:
        f, g = (g, divmodp(f, g)[1])
    return [a * pow(f[-1], -1, P) % P for a in f]

def roots_poly(roots):
    h = [1]
    for x in roots:
        h = mul(h, [-x, 1])
    return h

def seeds():
    eta = pow(G, N // 8, P)
    xs = [pow(eta, j, P) for j in range(8)]
    R = [roots_poly([xs[j] for j in ids]) for ids in [(0, 1, 5), (0, 3, 4), (1, 2, 3)]]
    h = ev(R[0], xs[6])
    assert h != 0
    polys = [[0], R[0]]
    for f in R[1:]:
        assert ev(f, xs[6]) != 0
        c = h * pow(ev(f, xs[6]), -1, P) % P
        polys.append([c * a % P for a in f])
    return (eta, xs, polys)

def parameters(s, parts):
    assert s % 2 == 0 and s >= 2
    roots = {j: 0 for j in range(8)}
    roots[4] = roots[5] = s // 2 - 1
    covers = {0: [([0, 1, 2], s)], 1: [([0, 1, 3], s)], 2: [([0, 3], s // 2)], 3: [([0, 2, 3], s)], 4: [([0, 2], s // 2)], 5: [([0, 1], s // 2)], 6: [([1, 2, 3], s)], 7: [([1, 2, 3], s)]}
    unused = {j: 0 for j in range(8)}
    unused[2] = s // 2
    unused[4] = unused[5] = 1
    cores = [0] * 4
    for j in range(8):
        assert roots[j] + unused[j] + sum((c for g, c in covers[j])) == s
        for i in range(4):
            cores[i] += roots[j]
        for g, c in covers[j]:
            assert g in parts[j]
            for i in g:
                cores[i] += c
    A = 11 * s // 2 - 2
    assert cores == [A] * 4 and A >= 4 * s
    R = sum(roots.values())
    assert R == s - 2
    ordinary = sum((c for gs in covers.values() for g, c in gs))
    fresh = sum((len(parts[j]) * unused[j] for j in range(8)))
    assert ordinary == 13 * s // 2 and fresh == 3 * s // 2 + 6
    D = ordinary + fresh
    assert D == 8 * s + 6
    assert D + 6 * A == 38 * s + 3 * R
    assert 38 * s + 3 * R - 6 * (A + 1) == 8 * s
    return {'n': 8 * s, 's': s, 'degree_B': R, 'degree_p': 4 * s - 2, 'degree_q': 4 * s - 1, 'common_roots_by_fiber': roots, 'uncovered_by_fiber': unused, 'exact_core_sizes': cores, 'support_size': A + 1, 'ordinary_directions': ordinary, 'fresh_directions': fresh, 'distinct_directions': D, 'unsafe_radius': [8 * s - A - 1, 8 * s], 'next_core_direction_upper_bound': 8 * s}

def main():
    assert P == N * (2 ** 128 + 192) + 1 and pow(G, N, P) == 1 and (pow(G, N // 2, P) != 1)
    eta, xs, polys = seeds()
    assert pow(eta, 8, P) == 1 and pow(eta, 4, P) == P - 1
    assert all((len(f) == 4 for f in polys[1:]))
    common = polys[1]
    for f in polys[2:]:
        common = gcdp(common, f)
    assert common == [1]
    parts = []
    for x in xs:
        groups = defaultdict(list)
        for i, f in enumerate(polys):
            groups[ev(f, x)].append(i)
        parts.append(list(groups.values()))
    expected = [[[0, 1, 2], [3]], [[0, 1, 3], [2]], [[0, 3], [1], [2]], [[0, 2, 3], [1]], [[0, 2], [1], [3]], [[0, 1], [2], [3]], [[0], [1, 2, 3]], [[0], [1, 2, 3]]]
    assert parts == expected
    pair_roots = []
    for i in range(4):
        for j in range(i):
            h = sub(polys[i], polys[j])
            ids = [a for a, x in enumerate(xs) if ev(h, x) == 0]
            assert len(ids) == 3 and len(h) == 4
            fact = roots_poly([xs[a] for a in ids])
            q, r = divmodp(h, fact)
            assert r == [0] and len(q) == 1 and (q[0] != 0)
            pair_roots.append({'pair': [j, i], 'root_exponents': ids, 'factor_scalar': q[0]})
    beta = [5, 5, 3, 5, 3, 3, 7, 7]
    weights = [0, 2, 2, 2]
    assert sum(beta) == 38 and sum(weights) == 6
    for b, gs in zip(beta, parts):
        assert b >= len(gs) and b + 3 >= sum(weights)
        for g in gs:
            assert b >= 1 + sum((weights[i] for i in g))
    prod = parameters(N // 8, parts)
    D = prod['distinct_directions']
    assert prod['exact_core_sizes'] == [738197502] * 4 and prod['support_size'] == 738197503
    assert prod['unsafe_radius'] == [335544321, N] and D == 1073741830
    assert Fraction(*prod['unsafe_radius']) == Fraction(5, 16) + Fraction(1, N)
    assert D * 2 ** 128 > P and P > 12 * N + 4
    result = {'status': 'PASS_EXACT_ORDER8_FOUR_SOURCE_PRODUCTION_CONSTRUCTION', 'prime': P, 'generator': G, 'eta': eta, 'primitive_polynomials': polys, 'primitive_gcd': common, 'partitions': parts, 'pair_root_factorizations': pair_roots, 'dual_beta': beta, 'dual_weights': weights, 'root_premium': 3, 'production': prod, 'security_margin': D * 2 ** 128 - P, 'parameter_controls': [parameters(s, parts) for s in [16, 64, 128]], 'scope': 'Exact production seed and parameter certificate plus written greedy/support proof; no full production expansion or Lean formalization.'}
    return result
if __name__ == '__main__':
    result = main()
    print(json.dumps(result, indent=2))
