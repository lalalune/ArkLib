#!/usr/bin/env python3
"""Exact mixed-antipodal counting audit for the companion upper construction.

This audits a specific, justified upper estimate for key SUPPORT, hence a
pigeonhole guarantee. Failure does not upper-bound an actual large joint
fibre. The note proves fixed-partial-pattern dominance for arbitrary cyclic
orbit sizes; no coefficient independence is assumed.
"""

from fractions import Fraction
from math import comb


P, N = 2130706433, 262144
BUDGET = P**6 // 2**128
TARGET = 139776


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def ceil_fraction(value):
    return (value.numerator + value.denominator - 1) // value.denominator


def mixed_counts(f, r, singles):
    h = f // 2
    assert (r - singles) % 2 == 0
    pairs = (r - singles) // 2
    # Ordinary cycles have two singleton choices. The reserved {1,-1}
    # cycle has only the -1 choice because the fine label zero is excluded.
    patterns_without_reserved = choose(h - 1, singles) * 2**singles
    patterns_with_reserved = choose(h - 1, singles - 1) * 2**(singles - 1) if singles else 0
    candidates = (patterns_without_reserved * choose(h - 1 - singles, pairs)
                  + patterns_with_reserved * choose(h - singles, pairs))
    patterns = patterns_without_reserved + patterns_with_reserved
    top = max(0, r - h - 2)
    coefficient_count = top // 2
    # Condition on a singleton pattern W. In W(Y)*H(Y^2), the prescribed
    # top coefficients use at most floor(top/2) coefficients of H; its
    # constant product ranges over at most h possibilities.
    key_support_bound = patterns * h * P**coefficient_count
    return candidates, key_support_bound, pairs, coefficient_count


def main():
    assert TARGET * 512 == 273 * N
    assert BUDGET == 274980728111395087
    assert P * P > 2**61
    # Internal combinatorial identity: the mixed symmetry classes partition
    # all r-subsets of the 2h-1 available fine labels.
    for f in (8, 16, 32, 64):
        for r in range(f):
            total = 0
            for singles in range(r % 2, min(r, f - r) + 1, 2):
                total += mixed_counts(f, r, singles)[0]
            assert total == choose(f - 1, r)
    best = None
    checked = 0
    for f in (64, 128, 256, 512, 1024, 2048, 4096):
        fine_size = N // f
        first_r = (TARGET + 1 + fine_size - 1) // fine_size - 1
        local_best = None
        # Later r values of each parity only decrease the same fixed-s
        # binomial counts and increase the key bound; see the note.
        for r in (first_r, first_r + 1):
            assert (r + 1) * fine_size - 1 >= TARGET
            for singles in range(r % 2, min(r, f - r) + 1, 2):
                candidates, keys, pairs, coefficients = mixed_counts(f, r, singles)
                if not candidates or not keys:
                    continue
                assert coefficients <= pairs
                checked += 1
                assert candidates <= BUDGET * keys
                value = Fraction(candidates, keys)
                record = (value, f, r, singles, pairs, coefficients)
                if local_best is None or value > local_best[0]:
                    local_best = record
                if best is None or value > best[0]:
                    best = record
        assert local_best is not None
        print(f"fine fibres={f}: best (r,s,a,k)={local_best[2:]}; ceiling guarantee={ceil_fraction(local_best[0])}")
    assert best[1:] == (512, 273, 1, 136, 7)
    assert ceil_fraction(best[0]) == 15053820
    # Pure coarse-fibre certificates: finite scales, then a uniform entropy
    # inequality covering all larger powers of two dividing N.
    for h in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
        coarse_size = N // h
        r = (TARGET + 1 + coarse_size - 1) // coarse_size - 1
        top = max(0, r - h // 2 - 2)
        assert choose(h - 1, r) <= BUDGET * h * P**top
    for exponent in range(13, 19):
        h = 2**exponent
        top = 17 * h // 512 - 2
        assert 61 * top - 2 * (h - 1) == 13 * h // 512 - 120 > 0
        # Therefore C(h-1,r) <= 2^(h-1) < p^top, independently of r
        # above the first agreement-improving threshold.
    print(f"Exact mixed pattern classes checked={checked}; binomial partition checks PASS")
    print(f"Best mixed support-bound guarantee={ceil_fraction(best[0])}; required strict budget={BUDGET}")
    print("Fixed partial patterns: proof reduces to a dominating pure coarse-fibre certificate")
    print("PASS: these counting refinements do not improve the companion upper score")
    print("Scope: nonlinear overlap/concentration of joint keys remains unbounded.")


if __name__ == "__main__":
    main()
