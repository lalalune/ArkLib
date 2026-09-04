#!/usr/bin/env python3
"""Exact product-label census for the companion F=256,r=136 OrbitPencil candidate.

Checks two independent methods (subset-sum DP and a Ramanujan-sum formula),
the binomial total, and the complement relation. The best product marginal
is less than 1+2^-127 times the mean; after division by the p^6 possible top
coefficient labels its pigeonhole guarantee is still over a factor four
short of the companion count budget. No claim about the joint-map maximum.
"""

from math import comb


F, R = 256, 136
P = 2130706433
BUDGET = P**6 // 2**128


def subset_dp(fibres, max_size):
    counts = [[0] * fibres for _ in range(max_size + 1)]
    counts[0][0] = 1
    for label in range(1, fibres):
        for size in range(min(max_size, label), 0, -1):
            previous, current = counts[size - 1], counts[size]
            for residue, value in enumerate(previous):
                current[(residue + label) % fibres] += value
    return counts


def ramanujan_two_power(order, residue):
    assert order > 0 and order & (order - 1) == 0
    if order == 1:
        return 1
    if residue % order == 0:
        return order // 2
    if residue % (order // 2) == 0:
        return -order // 2
    return 0


def fourier_formula(fibres, size):
    """Root-of-unity filter after excluding label zero; integer-only evaluation."""
    assert fibres > 0 and fibres & (fibres - 1) == 0 and 0 <= size < fibres
    orders = [2**j for j in range(fibres.bit_length())]
    answer = []
    for residue in range(fibres):
        numerator = 0
        for order in orders:
            length = size // order
            generating_coefficient = (-1) ** (size + length) * comb(fibres // order - 1, length)
            numerator += generating_coefficient * ramanujan_two_power(order, residue)
        assert numerator % fibres == 0
        answer.append(numerator // fibres)
    return answer


def main():
    counts = subset_dp(F, R)
    histogram = counts[R]
    assert histogram == fourier_formula(F, R)
    complement_size = F - 1 - R
    assert counts[complement_size] == fourier_formula(F, complement_size)
    total_label = sum(range(1, F)) % F
    assert total_label == 128 and complement_size == 119
    assert all(histogram[s] == counts[complement_size][(total_label - s) % F] for s in range(F))
    total = comb(F - 1, R)
    assert sum(histogram) == total
    maximum = max(histogram)
    maximizers = [s for s in range(F) if histogram[s] == maximum]
    assert maximizers == list(range(4, F, 8))
    excess = F * maximum - total
    assert excess > 0
    # Exact placement of the relative deviation from uniformity.
    assert excess * 2**127 < total < excess * 2**128
    assert BUDGET == 274980728111395087
    top_labels = P**6
    best_pigeonhole_guarantee = (maximum + top_labels - 1) // top_labels
    assert best_pigeonhole_guarantee <= BUDGET
    assert 4 * maximum < BUDGET * top_labels < 5 * maximum
    print(f"F={F},r={R}; DP and independent Ramanujan formula agree for every label")
    print(f"Binomial total={total}")
    print(f"Maximum product-fibre size={maximum}")
    print(f"Maximizers={maximizers}")
    print(f"F*maximum-total={excess}")
    print("Relative improvement over mean lies strictly between 2^-128 and 2^-127")
    print(f"Complement identity: size136,label s <-> size119,label(128-s) mod256 PASS")
    print(f"Best top-coefficient pigeonhole guarantee={best_pigeonhole_guarantee}")
    print(f"Required strict count budget={BUDGET}")
    print("Exact shortage: 4*maximum < budget*p^6 < 5*maximum")
    print("PASS: optimizing only the product marginal cannot certify this candidate")
    print("Scope: no upper bound on the largest JOINT coefficient/product fibre; no score improvement or prize closure.")


if __name__ == "__main__":
    main()
