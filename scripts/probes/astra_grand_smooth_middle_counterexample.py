#!/usr/bin/env python3
"""Exact checks for a field-uniform, smooth-domain middle-band counterexample.

The accompanying proof refutes F1RegionSyzygy.RegionMiddleExclusion, not the
Proximity Prize.  No finite sweep is used to infer field uniformity.  The sweep
independently checks root products, coefficient ranks, lifted syzygies, all
region faces, and an actual three-codeword received-word construction.

Run from the repository root with ordinary Python 3; only stdlib is used.
"""

from __future__ import annotations

import json


SEED_LABELS = ((0, 1, 2), (4, 5, 6), (8, 9, 10))
PROTH_P = 111 * 2**128 + 1


def trim(poly: list[int]) -> list[int]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def mul(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out)


def add(a: list[int], b: list[int], p: int) -> list[int]:
    return trim([
        ((a[j] if j < len(a) else 0) + (b[j] if j < len(b) else 0)) % p
        for j in range(max(len(a), len(b)))])


def eval_poly(poly: list[int], x: int, p: int) -> int:
    result = 0
    for a in reversed(poly):
        result = (x * result + a) % p
    return result


def from_roots(roots: list[int], p: int) -> list[int]:
    result = [1]
    for x in roots:
        result = mul(result, [-x % p, 1], p)
    return result


def lift(poly: list[int], m: int) -> list[int]:
    out = [0] * ((len(poly) - 1) * m + 1)
    out[::m] = poly
    return out


def rank_and_kernel(matrix: list[list[int]], p: int) -> tuple[int, list[int] | None]:
    """Exact Gaussian elimination; return one nonzero null vector, if any."""
    a = [[x % p for x in row] for row in matrix]
    ncols = len(a[0])
    pivots = []
    for col in range(ncols):
        pivot = next((row for row in range(len(pivots), len(a)) if a[row][col]), None)
        if pivot is None:
            continue
        row = len(pivots)
        a[row], a[pivot] = a[pivot], a[row]
        inv = pow(a[row][col], -1, p)
        a[row] = [(x * inv) % p for x in a[row]]
        for other in range(len(a)):
            if other != row and a[other][col]:
                coeff = a[other][col]
                a[other] = [(x - coeff * y) % p for x, y in zip(a[other], a[row])]
        pivots.append(col)
    free = next((col for col in range(ncols) if col not in pivots), None)
    if free is None:
        return len(pivots), None
    vec = [0] * ncols
    vec[free] = 1
    for row, col in enumerate(pivots):
        vec[col] = -a[row][free] % p
    assert any(vec)
    assert all(sum(x * y for x, y in zip(row, vec)) % p == 0 for row in matrix)
    return len(pivots), vec


def syzygy_matrix(polys: list[list[int]], degree: int) -> list[list[int]]:
    columns = []
    for poly in polys:
        for shift in range(max(0, degree - len(poly) + 2)):
            col = [0] * (degree + 1)
            col[shift:shift + len(poly)] = poly
            columns.append(col)
    assert columns
    return [list(row) for row in zip(*columns)]


def root_of_two_power_order(p: int, n: int) -> int:
    assert n > 1 and n & (n - 1) == 0 and (p - 1) % n == 0
    for base in range(2, 100):
        root = pow(base, (p - 1) // n, p)
        if pow(root, n, p) == 1 and pow(root, n // 2, p) != 1:
            return root
    raise AssertionError("bounded root search failed")


def check_prime(p: int) -> None:
    if p == PROTH_P:
        # Proth theorem: odd 111 < 2^128 and this exact congruence imply primality.
        assert 111 < 2**128
        assert pow(5, (p - 1) // 2, p) == p - 1
    else:
        assert p >= 2
        divisor = 2
        while divisor * divisor <= p:
            assert p % divisor != 0
            divisor += 1


def seed_check(p: int, zeta: int) -> tuple[list[list[int]], list[list[int]]]:
    assert pow(zeta, 16, p) == 1 and pow(zeta, 8, p) != 1
    iota = pow(zeta, 4, p)
    s = (1 + zeta + zeta * zeta) % p
    assert s and (zeta - 1) * s % p == (pow(zeta, 3, p) - 1) % p
    polys = [from_roots([pow(zeta, e, p) for e in labels], p) for labels in SEED_LABELS]
    for j, poly in enumerate(polys):
        alpha = pow(iota, j, p)
        assert poly == [(-pow(zeta, 3, p) * pow(alpha, 3, p)) % p,
                        (zeta * s * alpha * alpha) % p, (-s * alpha) % p, 1]
    # This particular minor is the independent proof of no constant syzygy.
    minor = [[poly[d] for poly in polys] for d in (3, 2, 1)]
    rank3, kernel3 = rank_and_kernel(minor, p)
    assert (rank3, kernel3) == (3, None)
    rank, vec = rank_and_kernel(syzygy_matrix(polys, 4), p)
    assert rank == 5 and vec is not None
    cofactors = [trim(vec[2 * j:2 * j + 2]) for j in range(3)]
    assert all(cofactor != [0] for cofactor in cofactors)
    total = [0]
    for poly, cofactor in zip(polys, cofactors):
        total = add(total, mul(poly, cofactor, p), p)
    assert total == [0]
    return polys, cofactors


def profile(m: int) -> dict[str, int]:
    assert m >= 4
    n, k, d, t, delta = 16 * m, 8 * m, 3 * m, 4 * m - 1, 4 * m
    private = (2 * m) // 3 + 2
    support = t + 2 * d + private
    assert 3 * d + t <= n
    assert d + 1 + t <= k
    assert n + 1 <= 3 * d + 2 * t
    assert d < delta <= (3 * d) // 2 - 2
    assert t < t + d and k - 1 < t + 2 * d
    assert k - 1 - (t + d) == m
    assert t + delta == k - 1
    assert 3 * d + t + 3 * private <= n
    assert support == (2 * n) // 3 + 1 and 3 * support > 2 * n
    return {"m": m, "n": n, "k": k, "a_b_c": d, "t": t,
            "minimal_product_degree": delta, "imbalance": (3 * d) // 2 - delta,
            "private_size": private, "assigned_agreement": support}


def full_check(p: int, m: int, exponent: int) -> dict[str, object]:
    params = profile(m)
    n, k, t = params["n"], params["k"], params["t"]
    omega = pow(root_of_two_power_order(p, n), exponent, p)
    domain = [pow(omega, j, p) for j in range(n)]
    assert len(set(domain)) == n and all(pow(x, n, p) == 1 for x in domain)
    zeta = pow(omega, m, p)
    seed, cofactors = seed_check(p, zeta)
    blocks = [set(e for e in range(n) if e % 16 in labels) for labels in SEED_LABELS]
    assert all(len(block) == 3 * m for block in blocks)
    assert all(not (blocks[a] & blocks[b]) for a in range(3) for b in range(a))
    lifted = [from_roots([domain[e] for e in sorted(block)], p) for block in blocks]
    assert lifted == [lift(poly, m) for poly in seed]
    rank_below, kernel_below = rank_and_kernel(syzygy_matrix(lifted, 4 * m - 1), p)
    assert rank_below == 3 * m and kernel_below is None
    rank_at, kernel_at = rank_and_kernel(syzygy_matrix(lifted, 4 * m), p)
    assert rank_at == 3 * m + 2 and kernel_at is not None
    total = [0]
    for poly, cofactor in zip(lifted, cofactors):
        total = add(total, mul(poly, lift(cofactor, m), p), p)
    assert total == [0]

    unused = sorted(set(range(n)) - set.union(*blocks))
    triple = set(unused[:t])
    unused = unused[t:]
    q = params["private_size"]
    private = [set(unused[j * q:(j + 1) * q]) for j in range(3)]
    assert all(len(part) == q for part in private)
    # AB, AC, BC are blocks 0, 1, 2.  The syzygy sum is zero.
    supports = [triple | blocks[0] | blocks[1] | private[0],
                triple | blocks[0] | blocks[2] | private[1],
                triple | blocks[1] | blocks[2] | private[2]]
    factor_t = from_roots([domain[e] for e in sorted(triple)], p)
    codewords = [[0], mul(factor_t, mul(lifted[0], lift(cofactors[0], m), p), p),
                 [(-a) % p for a in mul(factor_t, mul(lifted[1], lift(cofactors[1], m), p), p)]]
    assert len({tuple(poly) for poly in codewords}) == 3
    assert all(len(poly) <= k for poly in codewords)
    word = [None] * n
    for poly, support in zip(codewords, supports):
        assert len(support) == params["assigned_agreement"]
        for e in support:
            value = eval_poly(poly, domain[e], p)
            assert word[e] is None or word[e] == value
            word[e] = value
    word = [0 if value is None else value for value in word]
    counts = [sum(eval_poly(poly, x, p) == word[e] for e, x in enumerate(domain))
              for poly in codewords]
    assert all(count >= params["assigned_agreement"] for count in counts)
    return {"p": p, "m": m, "generator_exponent": exponent,
            "rank_below": rank_below, "rank_at": rank_at,
            "actual_agreements": counts, "p_gt_n_fourth": p > n**4,
            "seed_cofactors": cofactors if m == 4 and exponent == 1 else None}


def main() -> None:
    primes = (193, 257, 65537, PROTH_P)
    seed_checks = 0
    for p in primes:
        check_prime(p)
        root = root_of_two_power_order(p, 16)
        for exponent in range(1, 16, 2):
            seed_check(p, pow(root, exponent, p))
            seed_checks += 1
    cells = [(193, 4)] + [(p, m) for p in primes[1:] for m in (4, 8, 16)]
    results = []
    for p, m in cells:
        for exponent in (1, 3, 7, 16 * m - 1):
            results.append(full_check(p, m, exponent))
    production = profile(2**26)
    production_root = root_of_two_power_order(PROTH_P, production["n"])
    seed_check(PROTH_P, pow(production_root, 2**26, PROTH_P))
    assert PROTH_P > production["n"]**4
    print(json.dumps({"seed_generator_checks": seed_checks,
                      "full_domain_exact_checks": len(results),
                      "large_field_full_checks": sum(row["p_gt_n_fourth"] for row in results),
                      "profiles": [profile(m) for m in (4, 8, 16)],
                      "full_checks": results,
                      "production_arithmetic_and_root_only": production,
                      "production_prime": PROTH_P,
                      "scope": "RegionMiddleExclusion refuted; only three codewords, no prize bound"},
                     indent=2))


if __name__ == "__main__":
    main()
