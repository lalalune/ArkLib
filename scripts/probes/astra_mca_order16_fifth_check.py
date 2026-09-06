#!/usr/bin/env python3
"""Exact fixed-family fifth degree-seven exclusion; standard library only."""
from pathlib import Path
from itertools import combinations, product
from collections import Counter, defaultdict
from fractions import Fraction
import json
from astra_mca_order16_check import P, N, ETA, W, EXPECTED, ev, mul, counts, seed_checks

HERE = Path(__file__).resolve().parent
XS = [pow(ETA, j, P) for j in range(16)]


def enumerate_candidates():
    targets = []
    for j, groups in enumerate(EXPECTED):
        size = max(map(len, groups))
        targets.append([ev(W[g[0]], XS[j]) for g in groups if len(g) == size])
    assert sum(max(map(len, groups)) for groups in EXPECTED) == 43
    assert [len(values) for values in targets] == [1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]
    seen = set()
    candidates = {}
    hit_histogram = Counter()
    assignments = 0
    for ids in combinations(range(16), 8):
        basis = []
        for j in ids:
            poly, denominator = [1], 1
            for h in ids:
                if h != j:
                    poly = mul(poly, [-XS[h], 1])
                    denominator = denominator * (XS[j] - XS[h]) % P
            inverse = pow(denominator, -1, P)
            basis.append([v * inverse % P for v in poly])
        for values in product(*(targets[j] for j in ids)):
            assignments += 1
            poly = tuple(sum(v * row[d] for v, row in zip(values, basis)) % P for d in range(8))
            if poly in seen:
                continue
            seen.add(poly)
            matches = sum(ev(poly, x) in values for x, values in zip(XS, targets))
            hit_histogram[matches] += 1
            if matches >= 10:
                candidates[poly] = matches
    existing = {tuple(poly + [0] * (8 - len(poly))) for poly in W}
    assert existing.issubset(candidates)
    new_candidates = {poly: h for poly, h in candidates.items() if poly not in existing}
    assert assignments == 47619 and len(seen) == 43503
    assert dict(hit_histogram) == {8: 43254, 9: 240, 10: 5, 12: 4}
    assert len(new_candidates) == 5
    return new_candidates, {
        'interpolation_assignments': assignments,
        'distinct_interpolants': len(seen),
        'maximum_class_match_histogram': dict(hit_histogram),
        'existing_sources': len(existing),
        'new_candidates': len(new_candidates),
    }


def constraints(fifth):
    polynomials = W + [list(fifth)]
    states = []
    for j, x in enumerate(XS):
        classes = defaultdict(list)
        for i, poly in enumerate(polynomials):
            classes[ev(poly, x)].append(i)
        groups = list(classes.values())
        for group in groups:
            states.append((j, 'covered', group, int(len(groups) > 1)))
        states.append((j, 'uncovered', [], len(groups)))
        states.append((j, 'joint_root', list(range(5)), 0))
    nvars = len(states) + 1
    matrix, rhs = [], []

    def add(row, bound):
        matrix.append(row)
        rhs.append(bound)

    for j in range(16):
        row = [int(state[0] == j) for state in states] + [0]
        add(row, 1)
        add([-v for v in row], -1)
    add([int(state[1] == 'joint_root') for state in states] + [0], 1)
    add([-state[3] for state in states] + [0], -16)
    for i in range(5):
        add([-int(i in state[2]) for state in states] + [1], 0)
    objective = [0] * nvars
    objective[-1] = 1
    return matrix, rhs, objective


def check_dual(poly, certificate):
    matrix, rhs, objective = constraints(poly)
    weights = [Fraction(*pair) for pair in certificate['weights']]
    assert len(weights) == len(rhs) and all(y >= 0 for y in weights)
    for j, required in enumerate(objective):
        assert sum(y * row[j] for y, row in zip(weights, matrix)) >= required
    bound = sum(y * b for y, b in zip(weights, rhs))
    assert bound == Fraction(*certificate['bound'])
    assert bound <= Fraction(45, 4)
    return bound


def main():
    seed_checks()
    candidates, census = enumerate_candidates()
    saved = json.loads(HERE.joinpath('astra_mca_order16_fifth_certificate.json').read_text())
    certificates = {tuple(item['poly']): item for item in saved['candidates']}
    assert set(certificates) == set(candidates)
    bounds = []
    for poly, matches in candidates.items():
        item = certificates[poly]
        assert item['maximum_class_hits'] == matches
        bounds.append(check_dual(poly, item['dual']))
    s = N // 16
    current_core = counts(s)['core_sizes'][0]
    proposed_core = current_core + 1
    small_match_sum_bound = 56 * s - 8
    assert 5 * proposed_core > small_match_sum_bound
    assert Fraction(45, 4) * s < proposed_core
    result = {
        'status': 'PASS_EXACT_FIXED_ORDER16_FIFTH_DEGREE7_EXCLUSION',
        'scope': 'Adding one degree<=7 polynomial to these four fixed sources, with a common factor of degree<=s-2 and q_i=Xp_i; all five cores must improve and these sources must supply at least n+1 directions. Not universal MCA safety.',
        'census': census,
        'exact_dual_bounds': [[v.numerator, v.denominator] for v in bounds],
        'maximum_relaxed_core': [45, 4],
        'production': {
            's': s,
            'current_core': current_core,
            'proposed_core': proposed_core,
            'h_le_9_five_core_sum_bound': small_match_sum_bound,
            'h_le_9_required_sum': 5 * proposed_core,
            'h_ge_10_single_core_bound': 45 * s // 4,
        },
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
