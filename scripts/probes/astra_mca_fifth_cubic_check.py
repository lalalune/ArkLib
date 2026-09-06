#!/usr/bin/env python3
"""Verify the complete fifth-cubic extension exclusion using rational duals."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path

from astra_mca_four_cubic_check import P, N, seeds, ev, mul


def partitions(polynomials, nodes):
    result = []
    for x in nodes:
        classes = defaultdict(list)
        for i, polynomial in enumerate(polynomials):
            classes[ev(polynomial, x)].append(i)
        result.append(list(classes.values()))
    return result


def interpolation_candidates(polynomials, nodes):
    parts = partitions(polynomials, nodes)
    values = []
    for x, classes in zip(nodes, parts):
        sizes = [len(group) for group in classes]
        assert sizes.count(max(sizes)) == 1
        values.append(ev(polynomials[classes[sizes.index(max(sizes))][0]], x))
    assert sum(max(map(len, classes)) for classes in parts) == 21
    candidates = set()
    for support in combinations(range(8), 4):
        polynomial = [0] * 4
        for j in support:
            basis, denominator = [1], 1
            for h in support:
                if j != h:
                    basis = mul(basis, [-nodes[h], 1])
                    denominator = denominator * (nodes[j] - nodes[h]) % P
            scale = values[j] * pow(denominator, -1, P) % P
            for i, coefficient in enumerate(basis):
                polynomial[i] = (polynomial[i] + scale * coefficient) % P
        assert all(ev(polynomial, nodes[j]) == values[j] for j in support)
        candidates.add(tuple(polynomial))
    original = {tuple(poly + [0] * (4 - len(poly))) for poly in polynomials}
    assert len(candidates) == 44 and original <= candidates
    return candidates - original


def allocation_inequalities(polynomials, nodes):
    parts = partitions(polynomials, nodes)
    states = []
    for j, classes in enumerate(parts):
        for group in classes:
            states.append((j, 'covered', group, int(len(classes) > 1)))
        states.append((j, 'uncovered', [], len(classes)))
        states.append((j, 'root', list(range(5)), 0))
    rows, bounds = [], []
    for j in range(8):
        row = [int(state[0] == j) for state in states] + [0]
        rows.extend([row, [-entry for entry in row]])
        bounds.extend([1, -1])
    rows.append([int(state[1] == 'root') for state in states] + [0])
    bounds.append(1)
    rows.append([-state[3] for state in states] + [0])
    bounds.append(-8)
    for i in range(5):
        rows.append([-int(i in state[2]) for state in states] + [1])
        bounds.append(0)
    objective = [0] * len(states) + [1]
    return rows, bounds, objective


def verify():
    _, nodes, original = seeds()
    candidates = interpolation_candidates(original, nodes)
    fixture = json.loads(Path(__file__).with_name(
        'astra_mca_fifth_cubic_certificate.json').read_text())
    records = fixture['records']
    assert len(records) == len(candidates) == 40
    assert {tuple(record['polynomial']) for record in records} == candidates
    maximum_bound = Fraction(0)
    for record in records:
        rows, rhs, objective = allocation_inequalities(
            original + [record['polynomial']], nodes)
        dual = [Fraction(0)] * len(rows)
        indices = [entry[0] for entry in record['dual']]
        assert len(indices) == len(set(indices))
        for index, numerator, denominator in record['dual']:
            assert 0 <= index < len(rows) and denominator > 0
            dual[index] = Fraction(numerator, denominator)
        assert all(weight >= 0 for weight in dual)
        for j, coefficient in enumerate(objective):
            assert sum(dual[i] * rows[i][j] for i in range(len(rows))) >= coefficient
        bound = sum(weight * value for weight, value in zip(dual, rhs))
        assert bound == Fraction(*record['bound']) and bound <= Fraction(43, 8)
        maximum_bound = max(maximum_bound, bound)
    assert maximum_bound == Fraction(43, 8)
    s = N // 8
    target_core = 11 * s // 2 - 1
    # <=3 maximal-class hits cannot support five cores this large.
    assert 5 * target_core > 27 * s - 6
    # Every >=4-hit fifth cubic has its own exact dual certificate above.
    assert maximum_bound * s < target_core
    return {
        'status': 'PASS_EXACT_FIFTH_CUBIC_EXTENSION_EXCLUSION',
        'interpolants': 44,
        'distinct_fifth_sources': 40,
        'checked_rational_duals': 40,
        'largest_normalized_core_upper_bound': [43, 8],
        'production_improvement_required_core': target_core,
        'production_extension_core_upper_bound': int(maximum_bound * s),
        'scope': 'Five distinct cubics retaining the displayed four, common carrier q_i=Xp_i, '
                 'nonzero common factor of degree at most n/8-2, all five joint cores large, '
                 'and at least n+1 directions supplied by those sources. '
                 'Does not exclude other source families or additional decoders.'
    }


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
