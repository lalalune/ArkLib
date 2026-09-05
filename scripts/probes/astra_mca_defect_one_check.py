#!/usr/bin/env python3
"""Exact length-16 private-triple exclusion in the certified production field.

This is a bounded divisor census, not a scan of the production domain.
The accompanying note gives a separate cyclotomic norm argument.
Standard library only; no floating-point rank decisions.
"""

from itertools import combinations
import json
from math import comb

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478


def root_polynomial(indices, nodes):
    coefficients = [1]
    for index in indices:
        x = nodes[index]
        result = [0] * (len(coefficients) + 1)
        for j, value in enumerate(coefficients):
            result[j] = (result[j] - x * value) % P
            result[j + 1] = (result[j + 1] + value) % P
        coefficients = result
    return coefficients


def scan(n):
    assert n in (4, 16), "Only the documented bounded cases are enabled"
    d = (n - 1) // 3
    assert 3 * d + 1 == n
    generator = pow(G, 2**30 // n, P)
    assert pow(generator, n, P) == 1
    assert pow(generator, n // 2, P) == P - 1
    nodes = [pow(generator, j, P) for j in range(1, n)]
    assert len(set(nodes)) == n - 1 and 1 not in nodes
    polynomials = {
        sum(1 << i for i in indices): root_polynomial(indices, nodes)
        for indices in combinations(range(n - 1), d)
    }
    full = (1 << (n - 1)) - 1
    checked, hits, pivots = 0, [], {}
    # Each unordered partition has exactly one block containing index zero;
    # its next block is fixed by the smallest index outside that first block.
    for a_tail in combinations(range(1, n - 1), d - 1):
        a_mask = 1 + sum(1 << i for i in a_tail)
        rest = [i for i in range(n - 1) if not (a_mask >> i & 1)]
        for b_tail in combinations(rest[1:], d - 1):
            b_mask = (1 << rest[0]) + sum(1 << i for i in b_tail)
            c_mask = full ^ a_mask ^ b_mask
            assert not (a_mask & b_mask or a_mask & c_mask or b_mask & c_mask)
            assert a_mask.bit_count() == b_mask.bit_count() == c_mask.bit_count() == d
            a, b, c = [polynomials[mask] for mask in (a_mask, b_mask, c_mask)]
            ba = [(b[j] - a[j]) % P for j in range(d)]
            ca = [(c[j] - a[j]) % P for j in range(d)]
            pivot = next(j for j in range(d - 1, -1, -1) if ba[j])
            pivots[pivot] = pivots.get(pivot, 0) + 1
            checked += 1
            if all((ca[j] * ba[pivot] - ba[j] * ca[pivot]) % P == 0
                   for j in range(d)):
                alpha = ca[pivot] * pow(ba[pivot], -1, P) % P
                assert alpha not in (0, 1)
                assert all((c[j] - (1 - alpha) * a[j] - alpha * b[j]) % P == 0
                           for j in range(d + 1))
                hits.append(dict(masks=[a_mask, b_mask, c_mask], alpha=alpha,
                                 A=a, B=b, C=c))
    expected = comb(n - 2, d - 1) * comb(2 * d - 1, d - 1)
    assert checked == expected
    return dict(n=n, degree=d, generator=generator, missing_node=1,
                partitions=checked, hits=hits, pivot_counts=pivots)


def main():
    control, exclusion = scan(4), scan(16)
    assert control['partitions'] == len(control['hits']) == 1
    assert exclusion['partitions'] == 126126 and exclusion['hits'] == []
    assert exclusion['pivot_counts'] == {4: 126126}
    norm_bound = 400**8
    assert norm_bound == 655360000000000000000 and P > norm_bound
    print(json.dumps(dict(
        status='PASS_EXACT_LENGTH_16_DEFECT_ONE_EXCLUSION', prime=P,
        cases=[control, exclusion], cyclotomic_norm_bound=norm_bound,
        production_length_claim=False, lean_formalized=False,
        scope='Bounded exact census; norm extension uses the written proof'
    ), sort_keys=True))


if __name__ == '__main__':
    main()
