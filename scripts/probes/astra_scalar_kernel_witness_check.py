#!/usr/bin/env python3
"""Construct and independently verify a full finite differential interpolation kernel."""
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json
import re

import astra_mca_single_hole_locator_check as uni
from astra_scalar_differential_carrier_check import Poly, derivative, scalar_counts

P, N, W, A, M, CAP, D = 17, 13, 2, 5, 4, 2, 20
FIXTURE = Path(__file__).with_name("fixtures") / "astra_scalar_kernel_f17.json"
LEAN_CERTIFICATE = Path(__file__).with_name("astra_scalar_kernel_witness.lean")


def source_basis():
    return [(a, i, j) for j in range(CAP+1) for i in range((D-1)//W+1)
            for a in range(max(0, D-W*i-(W-1)*j))]


def received_word():
    return {x: (0 if x < 5 else x*x % P if x < 10 else {10: 3, 11: 7, 12: 11}[x])
            for x in range(N)}


def contact_column(monomial, word):
    """Direct multinomial coefficients for all nodes, retaining low contact weight."""
    a, i, j = monomial
    column = {}
    for node in range(N):
        for b in range(min(i, (M-1)//2)+1):
            for c in range(min(i-b, M-1-2*b)+1):
                scalar = comb(i, b)*comb(i-b, c)*pow(word[node], i-b-c, P)
                for tx in range(min(a, M-1-c-2*b)+1):
                    key = node, tx+c, b, j+c
                    value = scalar*comb(a, tx)*pow(node, a-tx, P) % P
                    column[key] = (column.get(key, 0)+value) % P
    return {key: value for key, value in column.items() if value}


def subtract(left, right, coefficient):
    for key, value in right.items():
        updated = (left.get(key, 0)-coefficient*value) % P
        if updated:
            left[key] = updated
        else:
            left.pop(key, None)


def construct_certificate():
    """Column elimination with exact combination tracking; no assumed kernel vector."""
    basis, word = source_basis(), received_word()
    pivots, nulls, prefix_ranks = {}, [], {}
    for index, monomial in enumerate(basis):
        column = contact_column(monomial, word)
        combination = {index: 1}
        while column:
            key = min(column)
            if key not in pivots:
                inverse = pow(column[key], -1, P)
                pivots[key] = ({k: v*inverse % P for k, v in column.items()},
                               {k: v*inverse % P for k, v in combination.items()})
                break
            old, old_combination = pivots[key]
            scalar = column[key]
            subtract(column, old, scalar)
            subtract(combination, old_combination, scalar)
        else:
            assert combination
            nulls.append(combination)
        prefix_ranks[monomial[2]] = len(pivots)
    assert len(basis) == 300 and len(pivots) == 295 and len(nulls) == 5
    assert prefix_ranks == {0: 110, 1: 210, 2: 295}
    # These are exactly the first dependency's coefficients, in basis order.
    terms = [list(basis[index])+[value] for index, value in sorted(nulls[0].items())]
    return {"field": P, "nodes": list(range(N)), "received": [word[x] for x in range(N)],
            "polynomial_degree_cap": W, "agreement_target": A,
            "contact_order": M, "R_cap": CAP, "weighted_cap": D,
            "basis_size": len(basis), "global_rank": len(pivots), "kernel_dimension": len(nulls),
            "global_ranks_at_R_caps_0_1_2": [prefix_ranks[j] for j in range(CAP+1)],
            "coefficient_format": "[X exponent, Y exponent, R exponent, coefficient modulo 17]",
            "Q_terms": terms}


def full_substitution_contact_check(Q, word):
    """Expand without contact truncation, independently of contact_column."""
    t = Poly({(1, 0, 0): 1})
    z = Poly({(0, 1, 0): 1})
    r = Poly({(0, 0, 1): 1})
    maximum_a = max(a for a, i, j in Q.terms)
    maximum_i = max(i for a, i, j in Q.terms)
    r_powers = [r**j for j in range(CAP+1)]
    for node in range(N):
        xp, yp = [Poly(1)], [Poly(1)]
        for _ in range(maximum_a):
            xp.append(xp[-1]*(t+node))
        for _ in range(maximum_i):
            yp.append(yp[-1]*(word[node]+t*r+z))
        expanded = Poly(0)
        for (a, i, j), coefficient in Q.terms.items():
            expanded = expanded+coefficient*xp[a]*yp[i]*r_powers[j]
        assert expanded != 0  # The coordinate substitution is invertible.
        assert min(tx+2*b for tx, b, j in expanded.terms) >= M
    return N


def verify_certificate(certificate):
    assert certificate == construct_certificate()
    lean_terms = LEAN_CERTIFICATE.read_text().split("-- BEGIN_Q_TERMS", 1)[1].split("-- END_Q_TERMS", 1)[0]
    assert [[int(x) for x in row] for row in re.findall(
        r"⟨\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)\s*⟩", lean_terms)] == certificate["Q_terms"]
    word = received_word()
    Q = Poly({tuple(row[:3]): row[3] for row in certificate["Q_terms"]})
    assert Q != 0 and len(Q.terms) == 249
    assert all(a+W*i+(W-1)*j < D and j <= CAP for a, i, j in Q.terms)
    assert Q.yr_degree() == 10 < P and W < P
    assert A*A < N*W  # Strictly beyond the ordinary Johnson agreement threshold.
    c, local_rank, _ = scalar_counts(D, W, M, CAP)
    assert (c, local_rank, c-N*local_rank) == (300, 23, 1)
    assert certificate["kernel_dimension"] >= c-N*local_rank
    node_checks = full_substitution_contact_check(Q, word)

    # Full field census, independent of interpolation subsets and the kernel.
    decoded = [uni.trim(f) for f in product(range(P), repeat=W+1)
               if sum(uni.evaluate(f, x) == word[x] for x in range(N)) >= A]
    assert decoded == [(0,), (0, 0, 1), (7, 15, 12)]
    Y = Poly({(0, 1, 0): 1})
    R = Poly({(0, 0, 1): 1})
    X = Poly({(1, 0, 0): 1})
    H = Q.derivative(2)
    G = -Q.derivative(0)-R*Q.derivative(1)
    # Common denominator H for w=2; coefficients of the reconstructed q(U).
    numerators = [H*Y-X*H*R+pow(2, -1, P)*X*X*G,
                  H*R-X*G, pow(2, -1, P)*G]
    for f in decoded:
        fp, fpp = derivative(f), derivative(derivative(f))
        assert Q.specialize(f, fp) == (0,)
        h = H.specialize(f, fp)
        assert h != (0,)
        assert G.specialize(f, fp) == uni.multiply(fpp, h)
        for j, numerator in enumerate(numerators):
            assert numerator.yr_degree() <= Q.yr_degree()
            assert numerator.specialize(f, fp) == uni.scale(f[j] if j < len(f) else 0, h)
    # In the same instance the complete lower-R-cap maps are injective.
    # This is stronger than their negative dimension-surplus tests alone.
    for cap, rank in enumerate(certificate["global_ranks_at_R_caps_0_1_2"][:2]):
        assert rank == sum(1 for a, i, j in source_basis() if j <= cap)
    digest = sha256(json.dumps(certificate, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"status": "PASS_EXPLICIT_BEYOND_JOHNSON_SCALAR_KERNEL",
            "n": N, "w": W, "agreement_target": A, "field": P,
            "source_columns": c, "global_rank": certificate["global_rank"],
            "actual_kernel_dimension": certificate["kernel_dimension"],
            "guaranteed_kernel_dimension": c-N*local_rank, "stored_Q_terms": len(Q.terms),
            "independent_full_contact_expansions": node_checks,
            "quadratic_polynomials_enumerated": P**(W+1),
            "complete_decoded_list": [list(f) for f in decoded],
            "regular_reconstructions": len(decoded), "Taylor_coefficient_checks": 9,
            "lower_R_caps_have_zero_kernel": [0, 1], "certificate_sha256": digest,
            "finite_Lean_data_match": True,
            "production_kernel_constructed": False, "independent_proof_review": False,
            "general_Lean_formalization": False, "prize_solved": False}


def main():
    certificate = json.loads(FIXTURE.read_text())
    print(json.dumps(verify_certificate(certificate), indent=2))


if __name__ == "__main__":
    main()
