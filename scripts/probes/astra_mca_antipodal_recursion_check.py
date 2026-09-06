#!/usr/bin/env python3
"""Exact algebra controls for the restricted antipodal-recursion obstruction.

Standard library only. Prints a deterministic JSON receipt and writes no files.
The universal statement is a written proof, not a consequence of this census.
"""
from collections import Counter
from itertools import permutations, product
import json

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478


def mul(f, g, p):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i + j] = (h[i + j] + a * b) % p
    return h


def ev(f, x, p):
    value = 0
    for a in reversed(f):
        value = (value * x + a) % p
    return value


def reflection(f, p):
    return [a if i % 2 == 0 else -a % p for i, a in enumerate(f)]


def odd_cross_coefficients(n, q, p):
    """After removing 2Y, the constant and Y^2 coefficients."""
    return ((n[1] * q[0] - n[0] * q[1]) % p,
            (n[1] * q[2] - n[2] * q[1]) % p)


def even_ratio(n, q, p):
    return odd_cross_coefficients(n, q, p) == (0, 0)


def proportional(n, q, p):
    return all((n[i] * q[j] - n[j] * q[i]) % p == 0
               for i in range(len(n)) for j in range(i))


def quadratic_controls(p):
    """All nonzero coefficient triples, including constants and linears."""
    polys = [f for f in product(range(p), repeat=3) if any(f)]
    counts = Counter()
    paired_points = [(r, t) for r in range(1, p) for t in range(r + 1, p)
                     if (r * r - t * t) % p]
    for n in polys:
        for q in polys:
            lhs_a = mul(n, reflection(q, p), p)
            lhs_b = mul(reflection(n, p), q, p)
            lhs = [(a - b) % p for a, b in zip(lhs_a, lhs_b)]
            u, v = odd_cross_coefficients(n, q, p)
            assert lhs == [0, 2 * u % p, 0, 2 * v % p, 0]
            counts['quadratic_pairs'] += 1
            if not u and not v:
                assert proportional(n, q, p) or n[1] == q[1] == 0
                counts['identically_even_ratios'] += 1
            for r, t in paired_points:
                if ev(lhs, r, p) == ev(lhs, t, p) == 0:
                    assert u == v == 0
                    counts['two_pair_vanishing_controls'] += 1
    return {'prime': p, 'projective_normalization': False,
            'antipodal_pair_choices': len(paired_points), **dict(counts)}


def linear_factor_controls(p):
    """All nonzero degree-at-most-one polynomials, up to nonzero scaling.

A constant is normalized to 1 and every genuine linear polynomial to Y-d.
Evenness and the forced-root conclusion are invariant under these scalings.
"""
    lines = [(1, 0)] + [((-d) % p, 1) for d in range(p)]
    counts = Counter()
    for b, c in permutations(range(1, p), 2):
        nb = [mul((-b % p, 1), line, p) for line in lines]
        qc = [mul((-c % p, 1), line, p) for line in lines]
        for i, l1 in enumerate(lines):
            for j, l2 in enumerate(lines):
                counts['first_ratio_cases'] += 1
                if not even_ratio(nb[i], qc[j], p):
                    continue
                counts['first_ratio_even'] += 1
                for a in range(1, p):
                    if a in (b, c):
                        continue
                    n2 = mul((-a % p, 1), l2, p)
                    for l3 in lines:
                        counts['second_ratio_cases'] += 1
                        q2 = mul((-b % p, 1), l3, p)
                        if not even_ratio(n2, q2, p):
                            continue
                        assert ev(l1, c, p) == 0
                        assert ev(l2, b, p) == 0
                        assert ev(l3, a, p) == 0
                        counts['both_ratios_even_forced_roots'] += 1
    return {'prime': p, 'linear_classes': len(lines), **dict(counts)}


def roots_poly(xs, indices, p):
    f = [1]
    for j in indices:
        f = mul(f, [-xs[j] % p, 1], p)
    return f


def rank_mod(rows, p):
    """Ordinary exact Gaussian elimination, without a numerical dependency."""
    rows = [row[:] for row in rows]
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], -1, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for i in range(rank + 1, len(rows)):
            factor = rows[i][col]
            if factor:
                rows[i] = [(x - factor * y) % p
                           for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def production_pattern_controls():
    """All specified 24*24 factor assignments; this is not all order-32 seeds."""
    eta = pow(G, 2 ** 25, P)
    assert pow(eta, 16, P) == P - 1 and pow(eta, 32, P) == 1
    xs = [pow(eta, j, P) for j in range(32)]
    assert len(set(xs)) == 32
    anchors = [0, 16, 24, 8]
    odd = (1, 3, 5, 7)
    ranks = Counter()
    first_witness = None
    for aa in permutations(odd):
        for bb in permutations(odd):
            sets = [[anchors[i]]
                    + [j for j in range(32) if j % 16 == 2 * aa[i]]
                    + [j for j in range(32) if j % 8 == bb[i]]
                    for i in range(4)]
            assert list(map(len, sets)) == [7] * 4
            assert len(set(j for ids in sets for j in ids)) == 28
            factors = [roots_poly(xs, ids, P) for ids in sets]
            for i, factor in enumerate(factors):
                assert len(factor) == 8 and factor[-1] == 1
                sparse = mul(mul([-xs[anchors[i]] % P, 1],
                                 [-pow(eta, 4 * aa[i], P) % P, 0, 1], P),
                             [-pow(eta, 4 * bb[i], P) % P, 0, 0, 0, 1], P)
                assert sparse == factor
                nonanchors = set(sets[i]) - {anchors[i]}
                assert all((j + 16) % 32 in nonanchors for j in nonanchors)
            A, B, C, _ = factors
            rows = []
            for j in sets[3]:
                x = xs[j]
                av, bv, cv = (ev(f, x, P) for f in (A, B, C))
                assert av and bv and cv
                # Unknowns are coefficients of l1, l2, l3, each constant first.
                # Triple equality on D gives B*l1=C*l2 and A*l2=B*l3.
                rows.append([bv, x * bv % P, -cv % P, -x * cv % P, 0, 0])
                rows.append([0, 0, av, x * av % P, -bv % P, -x * bv % P])
            rank = rank_mod(rows, P)
            assert rank == 6
            ranks[rank] += 1
            if first_witness is None:
                first_witness = {'quadratic_assignment': aa, 'quartic_assignment': bb,
                                 'root_exponents': sets, 'constraint_rank': rank}
    assert sum(ranks.values()) == 576
    return {'prime': P, 'eta32': eta, 'anchors': anchors,
            'checked_factor_assignments': sum(ranks.values()),
            'constraint_matrix_shape': [14, 6], 'rank_histogram': dict(ranks),
            'first_pattern': first_witness,
            'scope': 'Only the specified anchor/quadratic/quartic factor family; '
                     'full rank rules out every nonzero degree15 tuple in that family.',
            'primality': 'Uses the existing repository certificate for P; not reproved here.'}


def main():
    result = {
        'status': 'PASS_EXACT_ANTIPODAL_ALGEBRA_AND_576_RESTRICTED_PATTERNS',
        'quadratic_coefficient_controls': [quadratic_controls(p) for p in (3, 5, 7)],
        'forced_linear_factor_controls': [linear_factor_controls(p) for p in (5, 7, 11, 17)],
        'production_order32_controls': production_pattern_controls(),
        'proof_status': 'Universal obstruction is a written algebraic proof, not Lean-verified.',
        'scope': 'No attack, universal MCA safety bound, or unrestricted order32 nonexistence claim.'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
