from __future__ import annotations

import json
import math
import sys
import tomllib
import unicodedata
from itertools import combinations
from pathlib import Path

CASE_KEYS = {
    "artifact_id",
    "cells",
    "claimed_domain",
    "completeness_mode",
    "output_schema_version",
    "proof_id",
    "schema_version",
}
CELL_KEYS = {"cell_id", "n", "p"}
FIXED_CELLS = (
    ("p97-n3-even-m", 97, 3),
    ("p257-n4-even-m", 257, 4),
    ("p641-n5-even-m", 641, 5),
    ("p1297-n6-even-m", 1297, 6),
    ("p1459-n6-odd-m", 1459, 6),
    ("p2521-n7-even-m", 2521, 7),
)
CLAIMED_DOMAIN = [
    "exact prime-quadratic affine-intersection/cyclotomic-row transfer "
    "on the six frozen diagnostic cells"
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def canonical_bytes(value: object) -> bytes:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )
    return (unicodedata.normalize("NFC", encoded) + "\n").encode("utf-8")


def load_case(path: Path) -> list[tuple[str, int, int]]:
    document = tomllib.loads(path.read_text(encoding="utf-8"))
    require(type(document) is dict, "case must be a TOML table")
    require(set(document) == CASE_KEYS, "case fields do not match schema version 1")
    require(document["schema_version"] == 1, "case schema version changed")
    require(document["artifact_id"] == "CLM-043", "artifact binding changed")
    require(document["proof_id"] == "PRF-021", "proof binding changed")
    require(document["output_schema_version"] == 1, "output schema changed")
    require(
        document["completeness_mode"] == "six-cell-exact-diagnostics",
        "completeness mode changed",
    )
    require(document["claimed_domain"] == CLAIMED_DOMAIN, "claimed domain changed")
    raw_cells = document["cells"]
    require(type(raw_cells) is list, "cells must be an array of tables")
    parsed: list[tuple[str, int, int]] = []
    for raw_cell in raw_cells:
        require(type(raw_cell) is dict, "each cell must be a table")
        require(set(raw_cell) == CELL_KEYS, "cell fields do not match schema version 1")
        cell_id = raw_cell["cell_id"]
        p = raw_cell["p"]
        n = raw_cell["n"]
        require(type(cell_id) is str, "cell_id must be a string")
        require(type(p) is int and not isinstance(p, bool), "p must be an integer")
        require(type(n) is int and not isinstance(n, bool), "n must be an integer")
        parsed.append((cell_id, p, n))
    require(tuple(parsed) == FIXED_CELLS, "the frozen cells or their order changed")
    return parsed


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def prime_factors(value: int) -> tuple[int, ...]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    return tuple(factors)


def least_primitive_root(p: int) -> int:
    order = p - 1
    factors = prime_factors(order)
    for candidate in range(2, p):
        if all(pow(candidate, order // factor, p) != 1 for factor in factors):
            return candidate
    raise ArithmeticError("no primitive root found")


def character(value: int, p: int) -> int:
    residue = value % p
    if residue == 0:
        return 0
    symbol = pow(residue, (p - 1) // 2, p)
    if symbol == 1:
        return 1
    if symbol == p - 1:
        return -1
    raise ArithmeticError("quadratic-character evaluation failed")


def product(values: tuple[int, ...]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def exact_cell(cell_id: str, p: int, n: int) -> dict[str, object]:
    require(p % 2 == 1 and is_prime(p), "p must be an odd prime")
    require(n >= 3 and (p - 1) % n == 0, "n must divide p-1")
    require(p >= n**4, "the registered size condition p >= n^4 failed")

    subgroup = tuple(value for value in range(1, p) if pow(value, n, p) == 1)
    require(len(subgroup) == n, "n-th roots do not have cardinality n")
    subgroup_set = frozenset(subgroup)
    triples = tuple(combinations(subgroup, 3))
    six_subsets = tuple(combinations(subgroup, 6))
    squares = frozenset(value * value % p for value in range(1, p))
    one_minus_squares = frozenset((1 - value) % p for value in squares)

    direct_rows: dict[int, tuple[int, int, int, int, int]] = {}
    direct_u = 0
    d6 = 0
    affine_identity_rows = 0
    triple_identity_rows = 0
    inverse_root_zero_rows = 0
    inverse_root_zero_total = 0
    for t in range(1, p):
        values = tuple(character(1 - a * t, p) for a in subgroup)
        zero_count = sum(value == 0 for value in values)
        nonzero_count = sum(value * value for value in values)
        shifted_sum = sum(values)
        affine_count = len(
            frozenset(t * a % p for a in subgroup) & one_minus_squares
        )
        triple_sum = sum(
            product(tuple(character(1 - a * t, p) for a in triple))
            for triple in triples
        )
        cubic_numerator = shifted_sum**3 - (3 * nonzero_count - 2) * shifted_sum
        expected_zero = int(t in subgroup_set)
        require(zero_count == expected_zero, "inverse-root zero was lost or invented")
        require(
            nonzero_count == n - expected_zero,
            "nonzero count disagrees with inverse-root puncture",
        )
        require(
            shifted_sum == 2 * affine_count - nonzero_count,
            "S(t)=2C(t)-r(t) failed",
        )
        affine_identity_rows += 1
        require(cubic_numerator == 6 * triple_sum, "the exact cubic identity failed")
        triple_identity_rows += 1
        inverse_root_zero_rows += int(zero_count != 0)
        inverse_root_zero_total += zero_count
        direct_u += triple_sum * triple_sum
        d6 += math.factorial(6) * sum(
            product(tuple(character(1 - a * t, p) for a in subset))
            for subset in six_subsets
        )
        direct_rows[t] = (
            affine_count,
            nonzero_count,
            shifted_sum,
            triple_sum,
            zero_count,
        )

    require(tuple(direct_rows) == tuple(range(1, p)), "t=0 must be excluded exactly")
    require(inverse_root_zero_rows == n, "exactly the subgroup rows must contain zeros")
    require(inverse_root_zero_total == n, "each inverse-root row must contain one zero")

    m = (p - 1) // n
    square_subgroup = tuple(a for a in subgroup if character(a, p) == 1)
    h_size = len(square_subgroup)
    require(h_size > 0 and n % h_size == 0, "G intersect Q has invalid size")
    e = n // h_size
    require(e == (1 if m % 2 == 0 else 2), "parity branch for e failed")
    class_count = e * m
    require(class_count % 2 == 0, "class count must be even")
    primitive_root = least_primitive_root(p)
    classes = tuple(
        tuple(sorted(pow(primitive_root, index, p) * h % p for h in square_subgroup))
        for index in range(class_count)
    )
    require(
        all(len(elements) == h_size and len(set(elements)) == h_size for elements in classes),
        "a cyclotomic class has the wrong size",
    )
    flattened = tuple(value for elements in classes for value in elements)
    require(
        len(flattened) == p - 1 and set(flattened) == set(range(1, p)),
        "cyclotomic classes do not partition the punctured field",
    )
    class_index = {
        value: index for index, elements in enumerate(classes) for value in elements
    }
    for index, elements in enumerate(classes):
        sign = 1 if index % 2 == 0 else -1
        require(
            all(character(value, p) == sign for value in elements),
            "class parity does not equal the quadratic character",
        )

    subgroup_rows = tuple(unit * m for unit in range(e))
    reconstructed_subgroup = frozenset(
        value for index in subgroup_rows for value in classes[index]
    )
    require(reconstructed_subgroup == subgroup_set, "cyclotomic rows do not reconstruct G")

    intersection_rows: list[tuple[int, ...]] = []
    for elements in classes:
        counts = [0 for _ in range(class_count)]
        for value in elements:
            translated = (1 - value) % p
            if translated != 0:
                counts[class_index[translated]] += 1
        require(
            sum(counts) == h_size - int(1 in elements),
            "an inverse-root zero was not retained in N_(i,j)",
        )
        intersection_rows.append(tuple(counts))

    row_u_unweighted = 0
    cyclotomic_identity_rows = 0
    direct_cyclotomic_agreement_rows = 0
    for index, elements in enumerate(classes):
        shifted_sum = sum(
            (1 if column % 2 == 0 else -1) * count
            for unit in range(e)
            for column, count in enumerate(
                intersection_rows[(index + unit * m) % class_count]
            )
        )
        nonzero_count = n - int(index in subgroup_rows)
        cubic_numerator = shifted_sum**3 - (3 * nonzero_count - 2) * shifted_sum
        require(cubic_numerator % 6 == 0, "row cubic numerator is not divisible by six")
        triple_sum = cubic_numerator // 6
        cyclotomic_identity_rows += 1
        row_u_unweighted += triple_sum * triple_sum
        for t in elements:
            affine_count, direct_r, direct_s, direct_f, direct_zero = direct_rows[t]
            require(
                (direct_s, direct_r, direct_f)
                == (shifted_sum, nonzero_count, triple_sum),
                "a direct row disagrees with its cyclotomic class",
            )
            require(
                affine_count == (shifted_sum + nonzero_count) // 2,
                "the affine count is not reconstructed by its cyclotomic row",
            )
            require(
                direct_zero == int(index in subgroup_rows),
                "cyclotomic subgroup puncture disagrees with the inverse root",
            )
            direct_cyclotomic_agreement_rows += 1

    row_u = h_size * row_u_unweighted
    require(row_u == direct_u, "direct and cyclotomic U values disagree")
    remainder = d6 - 36 * direct_u
    remainder_bound = 87 * p * n**3
    require(abs(remainder) <= remainder_bound, "accepted D_6 remainder bound failed")
    return {
        "affine_identity_rows": affine_identity_rows,
        "cell_id": cell_id,
        "class_count": class_count,
        "cyclotomic_identity_rows": cyclotomic_identity_rows,
        "d6": d6,
        "direct_cyclotomic_agreement_rows": direct_cyclotomic_agreement_rows,
        "e": e,
        "h_size": h_size,
        "inverse_root_zero_rows": inverse_root_zero_rows,
        "inverse_root_zero_total": inverse_root_zero_total,
        "m": m,
        "n": n,
        "p": p,
        "remainder": remainder,
        "remainder_bound": remainder_bound,
        "subgroup_rows": list(subgroup_rows),
        "t_count": len(direct_rows),
        "t_max": max(direct_rows),
        "t_min": min(direct_rows),
        "triple_identity_rows": triple_identity_rows,
        "u": direct_u,
    }


def main(argv: list[str]) -> int:
    require(len(argv) == 1, "usage: reference.py case.toml")
    cells = load_case(Path(argv[0]))
    result = {
        "artifact_id": "CLM-043",
        "cells": [exact_cell(cell_id, p, n) for cell_id, p, n in cells],
        "completeness_mode": "six-cell-exact-diagnostics",
        "proof_id": "PRF-021",
        "schema_version": 1,
    }
    sys.stdout.buffer.write(canonical_bytes(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
