#!/usr/bin/env python3
"""Exact affine-span census for the smooth middle-band received word.

This excludes a fourth codeword only in span{f_B,f_C}, not in the full RS code.
The field-uniform proof is in astra_grand_stack_scope-2026-09-04.md.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path


SOURCE = Path(__file__).with_name("astra_grand_smooth_middle_counterexample.py")
SPEC = importlib.util.spec_from_file_location("smooth_middle", SOURCE)
assert SPEC is not None and SPEC.loader is not None
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)


def word_and_codewords(p: int, m: int) -> tuple[list[int], list[int], list[int]]:
    params = BASE.profile(m)
    n, t, q = params["n"], params["t"], params["private_size"]
    omega = BASE.root_of_two_power_order(p, n)
    domain = [pow(omega, j, p) for j in range(n)]
    seed, cofactors = BASE.seed_check(p, pow(omega, m, p))
    polys = [BASE.lift(poly, m) for poly in seed]
    blocks = [set(e for e in range(n) if e % 16 in labels) for labels in BASE.SEED_LABELS]
    unused = sorted(set(range(n)) - set.union(*blocks))
    triple, unused = set(unused[:t]), unused[t:]
    private = [set(unused[j * q:(j + 1) * q]) for j in range(3)]
    supports = [triple | blocks[0] | blocks[1] | private[0],
                triple | blocks[0] | blocks[2] | private[1],
                triple | blocks[1] | blocks[2] | private[2]]
    factor = BASE.from_roots([domain[j] for j in sorted(triple)], p)
    fb = BASE.mul(factor, BASE.mul(polys[0], BASE.lift(cofactors[0], m), p), p)
    fc = [-x % p for x in BASE.mul(
        factor, BASE.mul(polys[1], BASE.lift(cofactors[1], m), p), p)]
    values = [[0] * n, [BASE.eval_poly(fb, x, p) for x in domain],
              [BASE.eval_poly(fc, x, p) for x in domain]]
    word = [None] * n
    for vals, support in zip(values, supports):
        for j in support:
            assert word[j] is None or word[j] == vals[j]
            word[j] = vals[j]
    word = [0 if x is None else x for x in word]
    assert all(sum(a == b for a, b in zip(word, vals)) >= params["assigned_agreement"]
               for vals in values)
    return word, values[1], values[2]


def category(a: int, b: int, p: int) -> str:
    if b == 0:
        return "AB_edge"
    if a == 0:
        return "AC_edge"
    if (a + b) % p == 1:
        return "BC_edge"
    return "off_edges"


def check_cell(p: int, m: int, exhaustive: bool) -> dict[str, object]:
    BASE.check_prime(p)
    word, fb, fc = word_and_codewords(p, m)
    params = BASE.profile(m)
    t, q = params["t"], params["private_size"]
    bounds = {"AB_edge": t + 4 * m + q, "AC_edge": t + 4 * m + q,
              "BC_edge": 11 * m - 2 * q, "off_edges": 9 * m}
    assert max(bounds.values()) <= 10 * m < params["assigned_agreement"]
    if exhaustive:
        pairs = ((a, b) for a in range(p) for b in range(p))
    else:
        zeta = BASE.root_of_two_power_order(p, 16)
        samples = sorted({0, 1, 2, 3, p - 1, *(pow(zeta, j, p) for j in range(16))})
        pairs = iter(sorted({(a, b) for a in samples for b in samples} |
                            {(a, (1 - a) % p) for a in samples}))
    counts = {kind: 0 for kind in bounds}
    maxima = {kind: 0 for kind in bounds}
    maximizers = {}
    for a, b in pairs:
        if (a, b) in ((0, 0), (1, 0), (0, 1)):
            continue
        kind = category(a, b, p)
        agreement = sum((a * x + b * y - u) % p == 0 for u, x, y in zip(word, fb, fc))
        assert agreement <= bounds[kind], (p, m, a, b, agreement, bounds[kind])
        counts[kind] += 1
        if agreement > maxima[kind]:
            maxima[kind] = agreement
            maximizers[kind] = [a, b]
    if exhaustive:
        assert sum(counts.values()) == p * p - 3
    return {"p": p, "m": m, "exhaustive_coefficient_plane": exhaustive,
            "candidates_checked": sum(counts.values()), "counts_by_case": counts,
            "maximum_agreements_by_case": maxima, "maximizing_coefficients": maximizers,
            "proved_bounds_by_case": bounds, "required_agreement": params["assigned_agreement"]}


def main() -> None:
    cells = [check_cell(p, m, True) for p, m in ((193, 4), (257, 4), (257, 8))]
    cells += [check_cell(BASE.PROTH_P, m, False) for m in (4, 8, 16)]
    for m in (4, 8, 16, 2**26):
        params = BASE.profile(m)
        q = params["private_size"]
        assert 2 * q >= m and q <= 2 * m + 1
        assert max(9 * m, 11 * m - 2 * q, 8 * m - 1 + q) <= 10 * m
        assert 10 * m < params["assigned_agreement"]
    print(json.dumps({"scope": "Only affine span of three known codewords; full RS fourth remains open",
                      "cells": cells}, indent=2))


if __name__ == "__main__":
    main()
