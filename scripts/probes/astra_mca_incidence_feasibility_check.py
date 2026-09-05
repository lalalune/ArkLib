#!/usr/bin/env python3
"""Exact arithmetic checks of six-pencil incidence feasibility, not MCA witnesses."""

from itertools import combinations


def flat(labels):
    return frozenset(int(i) for i in labels)


def cyclic_cross(total):
    """Rows and columns sum to total, entries differ by at most one."""
    q, r = divmod(total, 3)
    return {
        frozenset((i + 1, j + 4)): q + int((j - i) % 3 < r)
        for i in range(3)
        for j in range(3)
    }


def two_disjoint(b):
    weights = cyclic_cross(2 * b - 2)
    weights.update({flat("123"): 2, flat("456"): 2})
    return weights


def one_triple(b):
    weights = cyclic_cross(2 * b - 4)
    weights.update({flat("123"): 4})
    weights.update({flat(pair): 2 for pair in ("45", "46", "56")})
    return weights


def weights_from(groups):
    return {flat(labels): value for labels, value in groups.items()}


def check(name, b, long_labels, weights):
    long_flats = [flat(labels) for labels in long_labels]
    labels = set(range(1, 7))
    assert all(len(a & c) <= 1 for a, c in combinations(long_flats, 2))
    allowed = {frozenset(), *(frozenset((i,)) for i in labels), *long_flats}
    allowed.update(
        frozenset(pair)
        for pair in combinations(sorted(labels), 2)
        if not any(set(pair) <= f for f in long_flats)
    )
    assert all(f in allowed and isinstance(w, int) and w >= 0 for f, w in weights.items())
    assert all(weights.get(f, 0) > 0 for f in long_flats)
    assert sum(weights.values()) == 6 * b - 2
    for i in labels:
        assert sum(w for f, w in weights.items() if i in f) == 2 * b
    for i, j in combinations(sorted(labels), 2):
        assert sum(w for f, w in weights.items() if {i, j} <= f) <= b - 2
    empty = weights.get(frozenset(), 0)
    singles = sum(w for f, w in weights.items() if len(f) == 1)
    triples = sum(w for f, w in weights.items() if len(f) == 3)
    quads = sum(w for f, w in weights.items() if len(f) == 4)
    assert triples + 2 * quads == 4 + singles + 2 * empty
    print(f"PASS {name}: b={b}, n={6*b-2}, positive flats={sum(w>0 for w in weights.values())}")


def main():
    check("one triple minimum", 6, ("123",), one_triple(6))
    check("two disjoint triples minimum", 4, ("123", "456"), two_disjoint(4))
    check("two intersecting triples minimum", 5, ("123", "145"), weights_from({
        "123": 3, "145": 3, "1": 2, "16": 2,
        "26": 2, "36": 2, "46": 2, "56": 2,
        "24": 3, "35": 3, "25": 2, "34": 2,
    }))
    check("three triangle triples minimum", 5, ("123", "145", "246"), weights_from({
        "123": 3, "145": 3, "246": 3,
        "16": 3, "25": 3, "34": 3,
        "35": 2, "36": 2, "56": 2,
        "1": 1, "2": 1, "4": 1, "": 1,
    }))
    check("four quadrilateral triples minimum", 5, ("123", "145", "246", "356"), weights_from({
        "123": 3, "145": 3, "246": 3, "356": 3,
        "16": 3, "25": 3, "34": 2,
        "1": 1, "6": 1, "2": 1, "5": 1, "3": 2, "4": 2,
    }))
    four_line = {flat("1234"): 6}
    four_line.update({frozenset((i, j)): 4 for i in range(1, 5) for j in (5, 6)})
    four_line.update({frozenset((i,)): 2 for i in range(1, 5)})
    check("four-point line minimum", 8, ("1234",), four_line)
    four_plus_three = {flat("1234"): 6, flat("156"): 1, flat("1"): 9}
    four_plus_three.update({frozenset((i, j)): 5 for i in (2, 3, 4) for j in (5, 6)})
    check("four-point line plus triple minimum", 8, ("1234", "156"), four_plus_three)

    production_b = 178956971
    for b in (4, 5, 6, 7, 8, 9, 10, 11, production_b):
        check("two-disjoint-triple formula", b, ("123", "456"), two_disjoint(b))
    for b in (6, 7, 8, 9, 10, 11, production_b):
        check("one-triple formula", b, ("123",), one_triple(b))

    b = production_b
    w = two_disjoint(b)
    branch_contribution = sum(t * (t - 1) // 2 for f, t in w.items() if len(f) >= 2)
    genus = (2 * b - 1) * (2 * b - 2) // 2
    assert branch_contribution == 2 * b * b - 7 * b + 8
    assert genus - branch_contribution == 4 * b - 7 == 715827877
    assert 6 * b - 2 == 2**30
    assert (2 * b - 2) // 4 == 89478485 and (2 * b - 2) % 4 == 0
    print("PASS production genus and private-locator degree arithmetic")
    print("Scope: exact incidence arithmetic only; no polynomial or MCA realization asserted.")


if __name__ == "__main__":
    main()
