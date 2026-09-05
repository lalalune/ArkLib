#!/usr/bin/env python3
"""Finite full-kernel escape certificates; requires NumPy.

See docs/kb/astra_full_kernel_properness-2026-09-05.md. These instances
do not prove universal properness or improve a prize bound.
"""
from collections import Counter
from itertools import combinations, product
import json
from math import comb

import numpy as np

from astra_acceleration_chart_check import U1
from astra_acceleration_extension_check import contact
from astra_hasse_order_two_check import coefficients, rank_one, rank_two
from astra_positive_kernel_factor_check import locator, add, scale, evaluate


def safe_dot(left, right, p):
    """Exact modular dot product using 15-bit limbs and signed int64."""
    a = np.asarray(left, dtype=np.int64)
    b = np.asarray(right, dtype=np.int64)
    base = 1 << 15
    assert 2 <= p <= 2130706433
    assert np.all((0 <= a) & (a < p)) and np.all((0 <= b) & (b < p))
    limb_max = max(min(p-1, base-1), (p-1)//base)
    assert a.shape[-1]*limb_max**2 < 2**63
    a0, a1, b0, b1 = a % base, a//base, b % base, b//base
    t00, t01 = (a0 @ b0) % p, (a0 @ b1) % p
    t10, t11 = (a1 @ b0) % p, (a1 @ b1) % p
    return (t00 + ((t01+t10) % p)*base + t11*(base*base % p)) % p


def nullspace(matrix, p):
    """Return a complete kernel basis as columns, with exact elimination."""
    a = np.array(matrix, dtype=np.int64, copy=True) % p
    nr, nc = a.shape
    pivots, row = [], 0
    for col in range(nc):
        candidates = np.flatnonzero(a[row:, col])
        if not len(candidates):
            continue
        pivot = row+int(candidates[0])
        a[[row, pivot]] = a[[pivot, row]]
        a[row, col:] = a[row, col:]*pow(int(a[row, col]), -1, p) % p
        indices = np.flatnonzero(a[row+1:, col])+row+1
        for start in range(0, len(indices), 64):
            selected = indices[start:start+64]
            a[selected, col:] = (
                a[selected, col:]-a[selected, col, None]*a[row, col:]) % p
        pivots.append(col)
        row += 1
        if row == nr:
            break
    pivot_set = set(pivots)
    free = [col for col in range(nc) if col not in pivot_set]
    out = np.zeros((nc, len(free)), dtype=np.int64)
    out[free, np.arange(len(free))] = 1
    for row, col in reversed(list(enumerate(pivots))):
        out[col, :] = -safe_dot(a[row, col+1:], out[col+1:, :], p) % p
    assert not np.any(safe_dot(np.asarray(matrix, dtype=np.int64) % p, out, p))
    return out


def basis(D, w, T, s1, s2):
    return [(x, i, j, k, z)
            for h in range(T+1) for i in range(h+1)
            for j in range(min(s1, h-i)+1)
            for k in range(min(s2, h-i-j)+1) for z in [h-i-j-k]
            for x in range(max(0, D-w*i-(w-1)*j-(w-2)*k))]


def local_columns(mons, m, p, node, u0, u1, order):
    """Contact expansion with powers cached across the complete source."""
    zero = (0, 0, 0, 0, 0)
    terms = {zero: u0, (0, 0, 0, 0, 1): u1,
             (1, 0, 1, 0, 0): 1, (0, 1, 0, 0, 0): 1}
    if order == 2:
        terms[2, 0, 0, 1, 0] = -1
    powers = [{zero: 1}]
    for _ in range(max(v[1] for v in mons)):
        out = {}
        for a, ca in powers[-1].items():
            for b, cb in terms.items():
                key = tuple(x+y for x, y in zip(a, b))
                if key[0]+(order+1)*key[1] < m:
                    out[key] = (out.get(key, 0)+ca*cb) % p
        powers.append({key: value for key, value in out.items() if value})
    columns = []
    for x, i, j, k, z in mons:
        out = {}
        for a in range(min(x, m-1)+1):
            cx = comb(x, a)*pow(node, x-a, p) % p
            for (t, v, r, s, zz), value in powers[i].items():
                if t+a+(order+1)*v < m:
                    key = (t+a, v, r+j, s+k, zz+z)
                    out[key] = (out.get(key, 0)+cx*value) % p
        columns.append({key: value for key, value in out.items() if value})
    return columns


def make_rows(columns):
    keys = sorted({key for column in columns for key in column})
    matrix = np.zeros((len(keys), len(columns)), dtype=np.int64)
    indices = {key: i for i, key in enumerate(keys)}
    for j, column in enumerate(columns):
        for key, value in column.items():
            matrix[indices[key], j] = value
    return keys, matrix


def full_kernel(p, direction, T, s1, s2, verify_direct=False):
    n, w, A, m, D = 9, 2, 5, 3, 15
    mons = basis(D, w, T, s1, s2)
    assert len(direction) == n and len(mons) == coefficients(D, w, T, s1, s2)
    assert p*p < 2**63
    order = 2 if s2 else 1
    blocks, errors = [], []
    # At the first A nodes, u0=0. The local map preserves the total
    # degree in (v,R,S,Z), so distinct homogeneous blocks cannot cancel.
    for h in range(T+1):
        ids = [c for c, mon in enumerate(mons) if sum(mon[1:]) == h]
        if not ids:
            continue
        block_basis = [mons[c] for c in ids]
        columns = [{} for _ in ids]
        for node in range(A):
            local = local_columns(block_basis, m, p, node, 0, direction[node], order)
            for col, entries in zip(columns, local):
                col.update({(node,)+key: value for key, value in entries.items()})
        _, matrix = make_rows(columns)
        partial = nullspace(matrix, p)
        if not partial.shape[1]:
            continue
        columns = [{} for _ in ids]
        for node in range(A, n):
            local = local_columns(block_basis, m, p, node, 1, direction[node], order)
            for col, entries in zip(columns, local):
                col.update({(node,)+key: value for key, value in entries.items()})
        keys, matrix = make_rows(columns)
        blocks.append((ids, partial))
        errors.append((keys, safe_dot(matrix, partial, p)))
    keys = sorted({key for block_keys, _ in errors for key in block_keys})
    indices = {key: i for i, key in enumerate(keys)}
    matrix = np.zeros((len(keys), sum(a.shape[1] for _, a in errors)), dtype=np.int64)
    offset = 0
    for block_keys, block in errors:
        for i, key in enumerate(block_keys):
            matrix[indices[key], offset:offset+block.shape[1]] = block[i]
        offset += block.shape[1]
    combined = nullspace(matrix, p)
    result = np.zeros((len(mons), combined.shape[1]), dtype=np.int64)
    offset = 0
    for ids, partial in blocks:
        result[ids, :] = safe_dot(partial, combined[offset:offset+partial.shape[1], :], p)
        offset += partial.shape[1]
    direct_columns = 0
    if verify_direct:
        # Compare every local column with the older, per-monomial
        # implementation and test the reconstructed basis at every node.
        for node in range(n):
            local = local_columns(mons, m, p, node, int(node >= A), direction[node], order)
            assert local == [contact(mon, node, int(node >= A), direction[node], m, p,
                                     order=order) for mon in mons]
            direct_columns += len(mons)
            _, full = make_rows(local)
            assert not np.any(safe_dot(full, result, p))
        assert nullspace(result, p).shape[1] == 0
    local_rank = (rank_two(D, w, T, m, s1, s2, p) if s2
                  else rank_one(D, w, T, m, s1))
    return mons, result, {
        "columns": len(mons), "local_rank": local_rank,
        "uniform_margin": len(mons)-n*local_rank, "nullity": result.shape[1],
        "T": T, "s1": s1, "s2": s2, "direct_column_checks": direct_columns,
    }


def values(mons, kernel, point, p, axis=None):
    out = []
    for mon in mons:
        mon, coefficient = list(mon), 1
        if axis is not None:
            coefficient = mon[axis]
            if not coefficient:
                out.append(0)
                continue
            mon[axis] -= 1
        for exponent, coordinate in zip(mon, point):
            coefficient = coefficient*pow(coordinate, exponent, p) % p
        out.append(coefficient)
    return safe_dot(np.asarray(out, dtype=np.int64), kernel, p)


def max_quadratic_agreement(direction, p):
    maximum = 0
    for triple in combinations(range(9), 3):
        f = []
        for node in triple:
            poly = locator([x for x in triple if x != node], p)
            f = add(f, scale(poly, direction[node]*pow(evaluate(poly, node, p), -1, p), p), p)
        maximum = max(maximum, sum(evaluate(f, x, p) == direction[x] % p for x in range(9)))
    return maximum


def case(name, direction, p, verify_direct=False):
    maximum = max_quadratic_agreement(direction, p)
    assert maximum < 5
    old_mons, old_kernel, old = full_kernel(p, direction, 6, 1, 0, verify_direct)
    assert old["uniform_margin"] == 1
    record = {"name": name, "p": p, "u1": direction,
              "maximum_quadratic_agreement": maximum, "old": old}
    # For A_i*R+B_i, a nonzero cross determinant excludes a common
    # positive-R factor. Checking four points is an escape search only.
    for x, y, z in ((19, 2, 3), (23, 5, 7), (31, 11, 13), (37, 17, 19)):
        a = values(old_mons, old_kernel, (x, y, 0, 0, z), p, 2)
        b = values(old_mons, old_kernel, (x, y, 0, 0, z), p)
        nonzero = np.flatnonzero(a)
        if len(nonzero):
            pivot = int(nonzero[0])
            cross = (a[pivot]*b-b[pivot]*a) % p
            hits = np.flatnonzero(cross)
            if len(hits):
                other = int(hits[0])
                return dict(record, status="no_common_positive_R_factor",
                            cross_witness={"point_X_Y_Z": [x, y, z], "pivot": pivot,
                                           "other": other, "value": int(cross[other])})
    # Every retained case without a cross witness has a unique old
    # generator. A single regular point identifies its positive-R factor.
    assert old_kernel.shape[1] == 1, "Need a symbolic common-factor analysis"
    new_mons, new_kernel, new = full_kernel(p, direction, 5, 3, 2, verify_direct)
    assert new["uniform_margin"] == 2
    points = [(11, 2, 3)] if verify_direct else product((11, 19, 23), (1, 2, 5, 7), (1, 3, 7, 11))
    for x, y, z in points:
        a = int(values(old_mons, old_kernel, (x, y, 0, 0, z), p, 2)[0])
        if not a:
            continue
        b = int(values(old_mons, old_kernel, (x, y, 0, 0, z), p)[0])
        r = -b*pow(a, -1, p) % p
        assert not np.any(values(old_mons, old_kernel, (x, y, r, 0, z), p))
        fx = int(values(old_mons, old_kernel, (x, y, r, 0, z), p, 0)[0])
        fy = int(values(old_mons, old_kernel, (x, y, r, 0, z), p, 1)[0])
        s = -(fx+r*fy)*pow(2*a, -1, p) % p
        evaluated = values(new_mons, new_kernel, (x, y, r, s, z), p)
        hits = np.flatnonzero(evaluated)
        if len(hits):
            index = int(hits[0])
            return dict(record, status="proper_pullback_found", new=new,
                        escape={"point_X_Y_R_S_Z": [x, y, r, s, z],
                                "new_basis_index": index, "value": int(evaluated[index])})
    raise AssertionError("Sampled points did not certify escape; no containment conclusion")


def arithmetic_controls():
    rng = np.random.default_rng(20260905)
    checks = 0
    for p in (17, 257, 65537, 2130706433):
        for inner in (0, 1, 3, 31, 1253):
            for boundary in (False, True):
                a = rng.integers(0, p, size=(4, inner), dtype=np.int64)
                b = rng.integers(0, p, size=(inner, 3), dtype=np.int64)
                if boundary:
                    a.fill(p-1)
                    b.fill(p-1)
                for left in (a, a[0]):
                    exact = (left.astype(object) @ b.astype(object)) % p
                    assert np.array_equal(safe_dot(left, b, p), exact)
                    checks += 1
    return checks


def main():
    arithmetic = arithmetic_controls()
    choices = [(f"reciprocal_{a}_{d}", [pow(pow(x+a, d, 257), -1, 257) for x in range(9)])
               for a in (1, 2, 3) for d in range(1, 9)]
    choices += [(f"power_{a}_{d}", [pow(x+a, d, 257) for x in range(9)])
                for a in (0, 1) for d in range(3, 9)]
    rng = np.random.default_rng(20260905)
    choices += [(f"random_{i}", [int(x) for x in rng.integers(1, 257, size=9)])
                for i in range(8)]
    finite = [case(name, direction, 257) for name, direction in choices]
    counts = dict(Counter(row["status"] for row in finite))
    assert counts == {"no_common_positive_R_factor": 5, "proper_pullback_found": 39}
    fixed = [case("fixed_acceleration_chart_direction", list(U1), p, verify_direct=True)
             for p in (257, 65537, 2130706433)]
    for row in fixed:
        assert row["old"]["nullity"] == 1 and row["new"]["nullity"] == 22
        assert row["status"] == "proper_pullback_found"
    print(json.dumps({"status": "PASS_FINITE_FULL_KERNEL_PROPERNESS",
                      "arithmetic_controls": arithmetic, "finite_counts": counts,
                      "finite_cases": finite, "fixed_direction_characteristics": fixed,
                      "production_properness_proved": False, "prize_bound_improved": False,
                      "independent_review_and_Lean_complete": False}, sort_keys=True))


if __name__ == "__main__":
    main()
