#!/usr/bin/env python3
"""
#444 N13/D2 probe: e2-recursion profile for dyadic roots of unity.

This is a bounded, exact cyclotomic-integer census.  It separates three lanes
that are easy to conflate in prose:

* e2(S)=0 and e1(S) != 0: the bad-scalar lane used by the monomial-pencil
  proximity obstruction.
* e1(S)=e2(S)=0: the stronger vanishing-subset / coset-union lane.
* the 2-singleton plus antipodal-doubles family handled by the Lean
  `_E2SquaringRecursion` reduction to subset sums on squared roots.

Arithmetic is in Z[zeta_n] with basis 1,zeta,...,zeta^(n/2-1) and
zeta^(n/2)=-1, so the counts are characteristic-zero structural counts, not
finite-field accidents.
"""

from collections import Counter
from itertools import combinations
from math import comb

MAX_SUBSETS = 1_200_000


def zero(n):
    return (0,) * (n // 2)


def add(u, v):
    return tuple(a + b for a, b in zip(u, v))


def root(j, n):
    half = n // 2
    e = j % n
    out = [0] * half
    if e < half:
        out[e] = 1
    else:
        out[e - half] = -1
    return tuple(out)


def mul_zeta(v):
    """Multiply a half-basis vector by zeta."""
    half = len(v)
    out = [0] * half
    for i, c in enumerate(v):
        ni = i + 1
        if ni < half:
            out[ni] += c
        else:
            out[0] -= c
    return tuple(out)


def orbit_count(vals):
    vals = set(vals)
    seen = set()
    sizes = Counter()
    orbits = 0
    for v in vals:
        if v in seen:
            continue
        orbits += 1
        cur = v
        size = 0
        while cur not in seen:
            seen.add(cur)
            cur = mul_zeta(cur)
            size += 1
        sizes[size] += 1
    return orbits, sizes


def pair_profile(S, n):
    half = n // 2
    present = set(S)
    doubles = 0
    singletons = 0
    for i in range(half):
        a = i in present
        b = (i + half) in present
        if a and b:
            doubles += 1
        elif a or b:
            singletons += 1
    return doubles, singletons


def e1_e2(S, roots, n):
    e1 = zero(n)
    e2 = zero(n)
    for i in S:
        e1 = add(e1, roots[i])
    for a, i in enumerate(S):
        for j in S[a + 1 :]:
            e2 = add(e2, roots[(i + j) % n])
    return e1, e2


def census(n, w):
    roots = [root(i, n) for i in range(n)]
    z = zero(n)
    total = comb(n, w)
    e2_zero = 0
    e1e2_zero = 0
    e2_nonzero_e1_values = set()
    profiles = Counter()
    recursion_family = 0
    recursion_family_e1_nonzero = 0

    for S in combinations(range(n), w):
        e1, e2 = e1_e2(S, roots, n)
        if e2 != z:
            continue
        e2_zero += 1
        profile = pair_profile(S, n)
        profiles[profile] += 1
        if profile[1] == 2:
            recursion_family += 1
        if e1 == z:
            e1e2_zero += 1
        else:
            e2_nonzero_e1_values.add(e1)
            if profile[1] == 2:
                recursion_family_e1_nonzero += 1

    orbit_n, orbit_sizes = orbit_count(e2_nonzero_e1_values)
    return {
        "n": n,
        "w": w,
        "total": total,
        "e2_zero": e2_zero,
        "e1e2_zero": e1e2_zero,
        "e2_e1_nonzero": e2_zero - e1e2_zero,
        "distinct_e1_nonzero": len(e2_nonzero_e1_values),
        "e1_orbits": orbit_n,
        "orbit_sizes": dict(sorted(orbit_sizes.items())),
        "profiles": dict(sorted(profiles.items())),
        "recursion_family": recursion_family,
        "recursion_family_e1_nonzero": recursion_family_e1_nonzero,
    }


def print_row(row):
    print(
        f"n={row['n']:>2} w={row['w']:>2} C={row['total']:>9} "
        f"e2=0:{row['e2_zero']:>6} "
        f"e1=e2=0:{row['e1e2_zero']:>5} "
        f"e2=0,e1!=0:{row['e2_e1_nonzero']:>6} "
        f"distinct-e1:{row['distinct_e1_nonzero']:>5} "
        f"e1-orbits:{row['e1_orbits']:>4}"
    )
    print(f"    pair profiles (doubles,singletons)->count: {row['profiles']}")
    print(
        "    2-singleton recursion family: "
        f"{row['recursion_family']} total, "
        f"{row['recursion_family_e1_nonzero']} with e1!=0; "
        f"orbit sizes {row['orbit_sizes']}"
    )


def main():
    print("=" * 88)
    print("#444 N13/D2 exact e2-recursion profile over Z[zeta_n]")
    print("=" * 88)
    print(f"enumeration cap: C(n,w) <= {MAX_SUBSETS}")
    print()

    cases = [
        (8, 4),
        (8, 5),
        (16, 4),
        (16, 5),
        (16, 8),
        (16, 12),
        (32, 4),
        (32, 5),
        (32, 6),
    ]

    rows = []
    for n, w in cases:
        total = comb(n, w)
        if total > MAX_SUBSETS:
            print(f"n={n:>2} w={w:>2} C={total:>9} SKIP above cap")
            continue
        row = census(n, w)
        rows.append(row)
        print_row(row)
        print()

    print("=" * 88)
    print("verdict")
    print("=" * 88)
    nonzero_rows = [r for r in rows if r["e2_zero"]]
    strict_smaller = [
        r
        for r in nonzero_rows
        if r["e1e2_zero"] < r["e2_zero"] and r["e2_e1_nonzero"] > 0
    ]
    partial_recursion = [
        r
        for r in nonzero_rows
        if r["recursion_family_e1_nonzero"] < r["e2_e1_nonzero"]
    ]
    print(
        "e1=e2=0 is strictly smaller than the e2=0 bad-scalar lane in "
        f"{len(strict_smaller)}/{len(nonzero_rows)} nonempty rows."
    )
    print(
        "The 2-singleton recursion family covers all e2=0,e1!=0 rows only when "
        f"{len(partial_recursion)} partial-coverage rows are absent; here partial rows = "
        f"{[(r['n'], r['w']) for r in partial_recursion]}."
    )
    print(
        "So a coset-union / generating-function proof must count e2=0,e1!=0 directly, "
        "or prove a separate injection from that lane into the stronger vanishing-subset lane. "
        "The current Lean recursion lemma is a useful local reduction, not a global closure."
    )


if __name__ == "__main__":
    main()
