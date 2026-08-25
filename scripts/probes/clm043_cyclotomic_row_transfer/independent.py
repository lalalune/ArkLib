from __future__ import annotations

import json
import sys
import tomllib
import unicodedata
from pathlib import Path

EXPECTED_METADATA = {
    "schema_version": 1,
    "artifact_id": "CLM-043",
    "proof_id": "PRF-021",
    "output_schema_version": 1,
    "completeness_mode": "six-cell-exact-diagnostics",
    "claimed_domain": [
        "exact prime-quadratic affine-intersection/cyclotomic-row transfer "
        "on the six frozen diagnostic cells"
    ],
}
EXPECTED_CELLS = [
    {"cell_id": "p97-n3-even-m", "p": 97, "n": 3},
    {"cell_id": "p257-n4-even-m", "p": 257, "n": 4},
    {"cell_id": "p641-n5-even-m", "p": 641, "n": 5},
    {"cell_id": "p1297-n6-even-m", "p": 1297, "n": 6},
    {"cell_id": "p1459-n6-odd-m", "p": 1459, "n": 6},
    {"cell_id": "p2521-n7-even-m", "p": 2521, "n": 7},
]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def parse_case(filename: str) -> list[dict[str, object]]:
    document = tomllib.loads(Path(filename).read_text(encoding="utf-8"))
    check(isinstance(document, dict), "case is not a mapping")
    cells = document.pop("cells", None)
    check(document == EXPECTED_METADATA, "case metadata is not the frozen schema")
    check(isinstance(cells, list), "cells are not an array")
    check(cells == EXPECTED_CELLS, "cell array is not the frozen six-cell domain")
    for cell in cells:
        check(type(cell["p"]) is int, "p is not an exact integer")
        check(type(cell["n"]) is int, "n is not an exact integer")
        check(type(cell["cell_id"]) is str, "cell_id is not a string")
    return cells


def json_line(value: object) -> bytes:
    text = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    return f"{unicodedata.normalize('NFC', text)}\n".encode()


def certify_prime(p: int) -> None:
    check(p >= 3 and p % 2 == 1, "p is not odd and at least three")
    candidate = 3
    while candidate <= p // candidate:
        check(p % candidate != 0, "p is composite")
        candidate += 2


def distinct_prime_divisors(number: int) -> list[int]:
    divisors: list[int] = []
    candidate = 2
    while candidate <= number // candidate:
        if number % candidate == 0:
            divisors.append(candidate)
            while number % candidate == 0:
                number //= candidate
        candidate += 1
    if number != 1:
        divisors.append(number)
    return divisors


def primitive_generator(p: int) -> int:
    order = p - 1
    prime_divisors = distinct_prime_divisors(order)
    generator = 2
    while generator < p:
        if not any(
            pow(generator, order // divisor, p) == 1
            for divisor in prime_divisors
        ):
            return generator
        generator += 1
    raise ArithmeticError("primitive generator search failed")


def chi(residue: int, p: int) -> int:
    residue %= p
    if residue == 0:
        return 0
    power = pow(residue, (p - 1) // 2, p)
    check(power in (1, p - 1), "Euler criterion produced an invalid value")
    return 1 if power == 1 else -1


def elementary_symmetric(values: tuple[int, ...], degree: int) -> int:
    coefficients = [1] + [0] * degree
    processed = 0
    for value in values:
        processed += 1
        for index in range(min(degree, processed), 0, -1):
            coefficients[index] += value * coefficients[index - 1]
    return coefficients[degree]


def evaluate(specification: dict[str, object]) -> dict[str, object]:
    cell_id = specification["cell_id"]
    p = specification["p"]
    n = specification["n"]
    check(type(cell_id) is str and type(p) is int and type(n) is int, "bad cell")
    certify_prime(p)
    check(n >= 3 and (p - 1) % n == 0, "n does not index a subgroup")
    check(p >= n**4, "p is below the fixed size threshold")

    m = (p - 1) // n
    e = 1 + (m % 2)
    check(e in (1, 2), "quadratic restriction index is invalid")
    class_count = e * m
    check(class_count % 2 == 0, "cyclotomic class count is odd")
    h_size = n // e
    check(h_size * e == n, "H index does not divide n")
    zeta = primitive_generator(p)
    h = tuple(sorted(pow(zeta, multiple * class_count, p) for multiple in range(h_size)))
    check(len(set(h)) == h_size, "H powers are not distinct")

    classes = tuple(
        tuple(sorted(pow(zeta, index, p) * element % p for element in h))
        for index in range(class_count)
    )
    universe = [element for row in classes for element in row]
    check(len(universe) == p - 1, "cyclotomic class cardinality failed")
    check(set(universe) == set(range(1, p)), "cyclotomic classes miss field elements")
    lookup: dict[int, int] = {}
    for row_index, elements in enumerate(classes):
        expected_character = 1 if row_index % 2 == 0 else -1
        for element in elements:
            check(element not in lookup, "cyclotomic classes overlap")
            lookup[element] = row_index
            check(
                chi(element, p) == expected_character,
                "cyclotomic row parity does not give chi",
            )

    subgroup_rows = tuple(unit * m for unit in range(e))
    subgroup = tuple(
        sorted(element for row_index in subgroup_rows for element in classes[row_index])
    )
    check(len(subgroup) == n and len(set(subgroup)) == n, "G reconstruction failed")
    check(all(pow(element, n, p) == 1 for element in subgroup), "G has a non-root")
    brute_roots = {element for element in range(1, p) if pow(element, n, p) == 1}
    check(set(subgroup) == brute_roots, "cyclotomic rows do not equal G")

    nij: list[dict[int, int]] = []
    for elements in classes:
        counts: dict[int, int] = {}
        for element in elements:
            translated = (1 - element) % p
            if translated == 0:
                continue
            column = lookup[translated]
            counts[column] = counts.get(column, 0) + 1
        check(
            sum(counts.values()) == h_size - int(1 in elements),
            "N_(i,j) did not retain the translated zero",
        )
        nij.append(counts)

    s_by_class: list[int] = []
    r_by_class: list[int] = []
    f_by_class: list[int] = []
    for index in range(class_count):
        shifted_sum = 0
        for unit in range(e):
            source_row = nij[(index + unit * m) % class_count]
            shifted_sum += sum(
                (1 if column % 2 == 0 else -1) * count
                for column, count in source_row.items()
            )
        nonzero_count = n - int(index in subgroup_rows)
        numerator = shifted_sum**3 - (3 * nonzero_count - 2) * shifted_sum
        check(numerator % 6 == 0, "six does not divide a row numerator")
        s_by_class.append(shifted_sum)
        r_by_class.append(nonzero_count)
        f_by_class.append(numerator // 6)

    cyclotomic_u = h_size * sum(value * value for value in f_by_class)
    squares = {value * value % p for value in range(1, p)}
    one_minus_squares = {(1 - value) % p for value in squares}
    subgroup_set = set(subgroup)
    t_values: list[int] = []
    inverse_root_zero_rows = 0
    inverse_root_zero_total = 0
    affine_identity_rows = 0
    triple_identity_rows = 0
    agreement_rows = 0
    direct_u = 0
    d6 = 0
    for t in range(1, p):
        t_values.append(t)
        values = tuple(chi(1 - element * t, p) for element in subgroup)
        zero_count = values.count(0)
        inverse_root_zero_rows += int(zero_count > 0)
        inverse_root_zero_total += zero_count
        r = sum(value * value for value in values)
        s = sum(values)
        affine_count = len({t * element % p for element in subgroup} & one_minus_squares)
        check(zero_count == int(t in subgroup_set), "inverse root check failed")
        check(r == n - zero_count, "nonzero character count failed")
        check(s == 2 * affine_count - r, "affine intersection identity failed")
        affine_identity_rows += 1

        f = elementary_symmetric(values, 3)
        check(s**3 - (3 * r - 2) * s == 6 * f, "cubic Newton identity failed")
        triple_identity_rows += 1
        direct_u += f * f
        d6 += 720 * elementary_symmetric(values, 6)

        row_index = lookup[t]
        check(
            (s, r, f)
            == (s_by_class[row_index], r_by_class[row_index], f_by_class[row_index]),
            "row reconstruction disagrees with the pointwise values",
        )
        check(
            affine_count == (s_by_class[row_index] + r_by_class[row_index]) // 2,
            "row reconstruction disagrees with C(t)",
        )
        agreement_rows += 1

    check(t_values == list(range(1, p)), "the punctured t-domain changed")
    check(0 not in t_values, "t=0 was included")
    check(inverse_root_zero_rows == n, "wrong number of inverse-root rows")
    check(inverse_root_zero_total == n, "inverse-root zeros are not unique")
    check(direct_u == cyclotomic_u, "direct and cyclotomic U disagree")
    remainder = d6 - 36 * direct_u
    remainder_bound = 87 * p * n**3
    check(abs(remainder) <= remainder_bound, "accepted D_6 remainder bound failed")
    return {
        "affine_identity_rows": affine_identity_rows,
        "cell_id": cell_id,
        "class_count": class_count,
        "cyclotomic_identity_rows": len(nij),
        "d6": d6,
        "direct_cyclotomic_agreement_rows": agreement_rows,
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
        "t_count": len(t_values),
        "t_max": max(t_values),
        "t_min": min(t_values),
        "triple_identity_rows": triple_identity_rows,
        "u": direct_u,
    }


def main(arguments: list[str]) -> None:
    check(len(arguments) == 1, "usage: independent.py case.toml")
    result = {
        "artifact_id": "CLM-043",
        "cells": [evaluate(cell) for cell in parse_case(arguments[0])],
        "completeness_mode": "six-cell-exact-diagnostics",
        "proof_id": "PRF-021",
        "schema_version": 1,
    }
    sys.stdout.buffer.write(json_line(result))


if __name__ == "__main__":
    main(sys.argv[1:])
