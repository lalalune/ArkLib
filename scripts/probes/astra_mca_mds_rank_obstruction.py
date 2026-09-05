#!/usr/bin/env python3
"""Exact support/degree audit for a generic MDS MCA obstruction at n=64.

No numerical code matrix is specialized. No production-length scan is run.
The written generic-matrix and MCA proof is in the companion KB note.
"""

from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path
import re


N, K, E, WIDTH = 64, 32, 20, 34
BLOCKS = [set((16*i+j) % N for j in range(21)) for i in range(4)]
NEIGHBORS = [BLOCKS[j//2] for j in range(8)] + [set(range(N)) for _ in range(26)]


def matching(rows):
    """Return column-to-row pairs for a maximum allowed-entry matching."""
    rows = set(rows)
    owner = {}

    def augment(column, seen):
        for row in sorted(NEIGHBORS[column] & rows):
            if row in seen:
                continue
            seen.add(row)
            if row not in owner or augment(owner[row], seen):
                owner[row] = column
                return True
        return False

    for column in range(WIDTH):
        augment(column, set())
    return sorted((column, row) for row, column in owner.items())


def main():
    minima = [min(len(set().union(*(BLOCKS[i] for i in subset)))
                  for subset in combinations(range(4), h)) for h in range(1, 5)]
    assert minima == [21, 37, 53, 64]
    assert N-K == K and (2*N+4)//3 == N-E == 44
    assert (2*N+4) % 3 == 0

    # For all 32-row subsets S, |U intersect S| >= max(0, |U|-32).
    # Adding the two dense L rows proves Hall for [G_S;L]. Any column
    # subset containing one of G's dense columns sees all 34 rows.
    sparse_subsets = []
    for mask in range(1, 1 << 8):
        columns = [j for j in range(8) if mask >> j & 1]
        union = set().union(*(NEIGHBORS[j] for j in columns))
        assert len(union) >= len(columns)  # Full G matching condition.
        assert max(0, len(union)-(N-K))+2 >= len(columns)
        sparse_subsets.append((columns, union))

    full = matching(range(N))
    assert len(full) == WIDTH
    minor_witnesses = []
    supports = set()
    for i, block in enumerate(BLOCKS):
        for x in sorted(block):
            error = block-{x}
            agreement = set(range(N))-error
            assert len(error) == E and len(agreement) == 44
            assert len(block & agreement) == 1
            assert tuple(sorted(error)) not in supports
            supports.add(tuple(sorted(error)))
            for columns, union in sparse_subsets:
                assert len(union & agreement) >= len(columns)-1
            witness = matching(agreement)
            assert len(witness) == WIDTH-1
            assert len({row for _, row in witness}) == WIDTH-1
            assert all(row in NEIGHBORS[column] & agreement for column, row in witness)
            minor_witnesses.append({"block": i, "deleted": x, "matching": witness})
    assert len(supports) == len(minor_witnesses) == 84

    terms = {
        "augmented_mds_minors": 34*comb(N, K),
        "full_ambient_minor": 34,
        "shortening_minors": 84*33,
        "block_row_minors": 4*comb(21, 2)*2,
        "finite_chart": 84*2,
        "distinct_quotient_directions": comb(84, 2)*4,
    }
    bound = sum(terms.values())
    assert bound == 62309220792048096754
    root = Path(__file__).resolve().parents[2]
    prime_source = root / "ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean"
    source = prime_source.read_text()
    p = int(re.search(r"abbrev P : ℕ := (\d+)", source).group(1))
    assert "theorem prime_P : Nat.Prime P" in source
    assert p == 2**158+192*2**30+1 and p > bound
    witnesses = json.dumps({"full": full, "shortenings": minor_witnesses}, sort_keys=True)
    print(json.dumps({
        "status": "PASS_FINITE_SUPPORT_AND_DEGREE_AUDIT_NOT_NUMERIC_MATRIX",
        "n": N, "k": K, "agreement_threshold": 44, "error_weight": E,
        "constructed_distinct_scalar_count_by_written_proof": 84,
        "support_union_minima": minima,
        "sparse_column_subsets_checked": len(sparse_subsets),
        "all_32_row_subsets_covered_by_uniform_hall_inequality": True,
        "full_matching_rank": len(full), "shortening_matching_count": len(minor_witnesses),
        "all_shortening_matching_ranks": 33,
        "matching_witnesses_sha256": sha256(witnesses.encode()).hexdigest(),
        "degree_terms": terms, "total_degree_upper_bound": bound,
        "production_field_modulus": p, "production_modulus_exceeds_degree_bound": True,
        "primality_source_only_not_rebuilt": str(prime_source.relative_to(root)),
        "scope": {
            "generic_mds_existence": True, "numerical_matrix_exhibited": False,
            "reed_solomon_realization_asserted": False,
            "production_length_counterexample_asserted": False, "lean_proof": False,
        },
    }, sort_keys=True))


if __name__ == "__main__":
    main()
