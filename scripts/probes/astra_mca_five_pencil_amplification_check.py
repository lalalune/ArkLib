#!/usr/bin/env python3
"""Exact five-pencil amplification and its restricted-family ceiling.

The production counts use written algebraic arguments and a fixed-degree
certificate. They are not a universal MCA bound or a Lean formalization.
"""

import json
from random import Random

from astra_mca_five_candidate_lift_check import (
    EXPECTED_ROOTS, base_certificate, compose_power, parity_weights,
)
from astra_mca_low_degree_saturation_check import determinant, gcd
from astra_mca_moment_rigidity_check import P, evaluate, mul, rank, root, subtract
from astra_mca_pair_basis_complete_check import scale


def primitives(base, p):
    z = base["zeta"]
    lines = base["lines"]
    ws = [(0,)] + [mul((-z % p, 0, 1), subtract(line, lines[0], p), p)
                   for line in lines[1:]]
    ws.append(scale(mul((-pow(z, 6, p) % p, 0, 1),
                        (-pow(z, 7, p) % p, 0, 1), p), -1, p))
    common = mul((1, 1), (-z*z % p, 0, 1), p)
    r = mul(common, (-z % p, 0, 1), p)
    fs = [mul(r, line, p) for line in lines] + [tuple(base["fifth_coefficients"])]
    assert all(subtract(mul(common, w, p), subtract(f, fs[0], p), p) == (0,)
               for w, f in zip(ws, fs))
    g = ws[1]
    for w in ws[2:]:
        g = gcd(g, w, p)
    assert list(g) == [1]
    for t in (1, z*z % p):
        # These values use T=Y^2 directly.
        vals = [0] + [((t-z)*(pow(z, i, p)-1)*(t-pow(z, -i, p))) % p
                      for i in range(1, 4)]
        assert len(set(vals)) == 4
    return ws


def base_cores(base):
    common = {1, 2, 8, 9, 10}
    return [common | set(a) for a in EXPECTED_ROOTS] + [set(base["fifth_base_domain_roots"])]


def pivot_columns(matrix, p):
    a = [list(row) for row in matrix]
    pivots = []
    for col in range(len(a[0])):
        r = len(pivots)
        pivot = next((j for j in range(r, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][col], -1, p)
        a[r] = [x*inv % p for x in a[r]]
        for j in range(r+1, len(a)):
            factor = a[j][col]
            a[j] = [(x-factor*y) % p for x, y in zip(a[j], a[r])]
        pivots.append(col)
        if len(pivots) == len(a):
            break
    return pivots


def rank_certificate():
    base, _ = base_certificate(P)
    eta, z = base["eta"], base["zeta"]
    cores = base_cores(base)[:4]
    rows = []
    for j in range(1, 16):
        owners = [i for i, core in enumerate(cores) if j in core]
        assert len(owners) >= 2
        powers = [pow(eta, j*a, P) for a in range(9)]
        for owner in owners[1:]:
            row = [0]*27
            for idx, sign in ((owner, 1), (owners[0], -1)):
                if idx:
                    row[(idx-1)*9:idx*9] = [sign*x % P for x in powers]
            rows.append(row)
    assert len(rows) == 25 and rank(rows, P) == 25
    cols = pivot_columns(rows, P)
    minor = [[row[c] for c in cols] for row in rows]
    det = determinant(minor, P)
    assert len(cols) == 25 and det
    r = mul(mul((1, 1), (-z % P, 0, 1), P), (-z*z % P, 0, 1), P)
    vector = [mul(r, subtract(line, base["lines"][0], P), P)
              for line in base["lines"][1:]]
    assert all(len(f) == 8 for f in vector)
    first = sum((list(f)+[0]*(9-len(f)) for f in vector), [])
    second = sum(([0]+list(f) for f in vector), [])
    assert rank([first, second], P) == 2
    assert all(sum(x*y for x, y in zip(row, v)) % P == 0
               for row in rows for v in (first, second))
    return {"rows": 25, "columns": 27, "rank": 25, "kernel_dimension": 2,
            "minor_columns_zero_based": cols, "minor_determinant": det,
            "kernel_is_seed_and_Y_times_seed": True}


def chart(values, n, p):
    for t in range(1, 257):
        if any((t-v) % p == 0 for v in values):
            continue
        gammas = [v*pow((t-v) % p, -1, p) % p for v in values]
        if len(set(gammas)) != 5:
            continue
        tests = [None if not a else pow(-pow(a, -1, p) % p, n, p) for a in gammas]
        if all(a is None or a != 1 for a in tests):
            return {"hole_u0": 0, "hole_u1": t, "private_scalars": gammas,
                    "ordinary_preimage_nth_powers": tests}
    raise AssertionError("No private chart found in the stated bounded search")


def dense_control(n, p):
    s, d, k = n//16, n//8, n//2
    base, _ = base_certificate(p)
    ws = primitives(base, p)
    z, g = base["zeta"], root(n, p)
    assert pow(g, s, p) == base["eta"]
    nodes = [pow(g, j, p) for j in range(n)]
    even_sum = tuple(1 if a % 2 == 0 else 0 for a in range(d-1))
    b = mul(even_sum, (-z*z % p,)+(0,)*(d-1)+(1,), p)
    fs = [mul(b, compose_power(w, s), p) for w in ws]
    gs = [(0,)+f for f in fs]
    assert max(len(f)-1 for f in fs) == k-2
    assert max(len(f)-1 for f in gs) == k-1
    values = [[evaluate(f, x, p) for x in nodes] for f in fs]
    cores = [{j for j in range(1, n) if j % 16 == 0 or j % 16 in a}
             for a in base_cores(base)]
    for core in cores[:4]:
        core.remove(n//2)
    assert [len(c) for c in cores] == [11*s-2]*4+[12*s-1]
    private = chart([v[0] for v in values], n, p)
    u0, u1 = [0]*n, [0]*n
    u1[0] = private["hole_u1"]
    for j in range(1, n):
        owners = [i for i, c in enumerate(cores) if j in c]
        assert owners
        assert len({values[i][j] for i in owners}) == 1
        u0[j] = values[owners[0]][j]
        u1[j] = nodes[j]*u0[j] % p
    witnesses = {}
    for j in range(1, n):
        absent = next((i for i in range(5) if values[i][j] != u0[j]), None)
        if absent is not None:
            gamma = -pow(nodes[j], -1, p) % p
            assert gamma not in witnesses
            witnesses[gamma] = (absent, j)
    assert len(witnesses) == 12*s+1
    for i, gamma in enumerate(private["private_scalars"]):
        assert gamma not in witnesses
        witnesses[gamma] = (i, 0)
    assert len(witnesses) == 12*s+6
    threshold = 11*s-1
    for gamma, (i, extra) in witnesses.items():
        support = sorted(cores[i])[:threshold-1]+[extra]
        assert len(set(support)) == threshold and extra not in cores[i]
        assert all((u0[j]+gamma*u1[j]-(1+gamma*nodes[j])*values[i][j]) % p == 0
                   for j in support)
        short = support[:k]+[extra]
        weights = parity_weights([nodes[j] for j in short], p)
        powers = [1]*len(short)
        for _ in range(k):
            assert sum(a*x for a, x in zip(weights, powers)) % p == 0
            powers = [a*nodes[j] % p for a, j in zip(powers, short)]
        sy0 = sum(a*u0[j] for a, j in zip(weights, short)) % p
        sy1 = sum(a*u1[j] for a, j in zip(weights, short)) % p
        assert sy0 or sy1
        assert (sy0+gamma*sy1) % p == 0
    return {"n": n, "prime": p, "candidate_degree_caps": [k-2, k-1],
            "core_sizes": [len(c) for c in cores], "event_agreement": threshold,
            "ordinary_scalars": 12*s+1, "private_scalars": private,
            "all_witness_parity_checks": len(witnesses),
            "distinct_certified_bad_scalars": len(witnesses),
            "full_MCA_bad_set_enumerated": False}


def production():
    n, s = 2**30, 2**26
    base, _ = base_certificate(P)
    ws = primitives(base, P)
    b1 = s*(1-base["zeta"]**2) % P
    values = [b1*evaluate(w, 1, P) % P for w in ws]
    assert b1 and len(set(values)) == 5
    private = chart(values, n, P)
    l, m = (s-1)//3, (4*s-1)//3
    assert 3*l == s-1 and 3*m == 4*s-1
    z = 4*s-1-(4*l)//3
    u = 1+2*l
    ceiling = n-z+4*u
    assert 4*l < 2*s and 4*s-m-8*l == 3
    assert ceiling < n and (12*s+6)*2**128 < P
    return {"n": n, "prime": P, "source_degrees": [8*s-2, 8*s-1],
            "core_sizes": [11*s-2]*4+[12*s-1],
            "event_agreement": 11*s-1, "radius_numerator": 5*s+1,
            "radius_denominator": n, "ordinary_scalars": 12*s+1,
            "private_chart": private, "distinct_certified_bad_scalars": 12*s+6,
            "exceeds_security_budget": False,
            "restricted_perturbation": {
                "first_four_losses_each": l, "fifth_losses": m,
                "source_degree_gap": 2*s, "first_four_union_bound": 4*l,
                "fifth_root_surplus": 3, "forced_zero_nodes": z,
                "uncovered_nodes_bound": u, "bad_scalar_ceiling": ceiling,
                "margin_below_budget": n-ceiling},
            "production_domain_enumerated": False,
            "full_MCA_bad_set_count_claimed": False}


def perturbation_controls():
    n, s, k = 64, 4, 32
    base, _ = base_certificate(P)
    ws, g = primitives(base, P), root(n, P)
    nodes = [pow(g, j, P) for j in range(n)]
    cores = [{j for j in range(1, n) if j % 16 == 0 or j % 16 in a}
             for a in base_cores(base)]
    fifth_drop = set(sorted(cores[4])[:5])
    patterns = [
        [set([32]) for _ in range(4)]+[fifth_drop],
        [{5}, {13}, {13}, {5}, fifth_drop],
        [{32}, {32}, {32}, {2}, {32, 2, 3, 4, 6}],
    ]
    rng = Random(20260905)
    for _ in range(3):
        patterns.append([{rng.choice(sorted(c))} for c in cores[:4]]
                        + [set(rng.sample(sorted(cores[4]), 5))])
    outcomes = []
    for drops in patterns:
        assert all(d <= c for d, c in zip(drops, cores))
        kept = [c-d for c, d in zip(cores, drops)]
        rows, forced = [], set()
        for j, x in enumerate(nodes):
            owners = [i for i, c in enumerate(kept) if j in c]
            if len(owners) < 2:
                continue
            powers = [pow(x, a, P) for a in range(k)]
            w_values = [evaluate(ws[i], pow(x, s, P), P) for i in owners]
            if len(set(w_values)) > 1:
                forced.add(j)
            for owner in owners[1:]:
                row = [0]*(4*k)
                for idx, sign in ((owner, 1), (owners[0], -1)):
                    if idx:
                        row[(idx-1)*k:idx*k] = [sign*a % P for a in powers]
                rows.append(row)
        dimension = 4*k-rank(rows, P)
        assert dimension == 4*s-len(forced)
        uncovered = n-len(set().union(*kept))
        assert len(forced) >= 14 and uncovered <= 3
        assert n-len(forced)+4*uncovered <= 62
        outcomes.append({"removed_indices": [sorted(d) for d in drops],
                         "retained_core_sizes": [len(c) for c in kept],
                         "full_source_columns": 4*k, "full_source_rows": len(rows),
                         "full_source_kernel_dimension": dimension,
                         "predicted_multiplier_dimension": 4*s-len(forced),
                         "forced_zero_nodes": len(forced), "uncovered_nodes": uncovered})
    return outcomes


def main():
    result = {"status": "PASS_FIVE_PENCIL_AMPLIFICATION_CONTROLS",
              "base_rank_certificate": rank_certificate(),
              "dense_controls": [dense_control(n, P) for n in (16, 64, 256)]
                                + [dense_control(64, 65537)],
              "dense_perturbation_controls": perturbation_controls(),
              "production": production(), "Lean_formalized": False,
              "independent_agent_reviewed": True, "externally_peer_reviewed": False,
              "audited_mathematical_source_commit": "ca77ac1069ae7c7f2adef6a803010f454d9f3c32",
              "prize_solved": False}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
