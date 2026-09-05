#!/usr/bin/env python3
"""Exact controls for the written fully split error-polynomial sublist bound.

This does not bound candidates whose error polynomial has roots outside mu_n.
The production certificate checks arithmetic intervals, not all received words.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement
import json

from astra_mca_moment_rigidity_check import (
    G, P, determinant, evaluate, locator, mul, rank, root, subtract,
)


def parameters(n):
    assert n >= 16 and n & (n-1) == 0 and n % 6 == 4
    k, b, ell = n//2, (n+2)//6, n//4
    return k, b, ell, k+b


def sublist_cap(n, degree):
    k, b, ell, A = parameters(n)
    assert A <= degree <= n-2
    return 3 if degree < 3*ell else (1 if degree < k+2*b+1 else 2)


def production_certificate():
    n = 2**30
    k, b, ell, A = parameters(n)
    maximum_excess = n-2-A
    assert P == n*(2**128+192)+1 and P > 2**158
    assert pow(G, n, P) == 1 and pow(G, n//2, P) != 1
    intervals = [(0, 0)]+[(2**j, min(2**(j+1)-1, maximum_excess))
                          for j in range(maximum_excess.bit_length())]
    assert intervals[0][0] == 0 and intervals[-1][1] == maximum_excess
    assert all(left[1]+1 == right[0] for left, right in zip(intervals, intervals[1:]))
    rows, checks = [], 0
    for lower, upper in intervals:
        gates = []
        m = n
        while m >= 8:
            # Lower moment count and upper excess norm cover this whole interval.
            h = (b+lower)*m//n
            r = (h+1)//2
            excess = 2*upper*m//n
            norm_squared = 2*m+4*excess+excess**2
            bits = (norm_squared-1).bit_length()
            assert 1 <= h < m and norm_squared <= 2**bits
            slack = 632*r-bits*m
            assert slack >= 0  # 316*r >= bits*(m/2)
            gates.append((slack, m, bits, r))
            checks += 1
            m //= 2
        # Compare the rational normalized slacks using exact cross-products.
        tightest = gates[0]
        for gate in gates[1:]:
            if gate[0]*tightest[1] < tightest[0]*gate[1]:
                tightest = gate
        rows.append({"excess_lower": lower, "excess_upper": upper,
                     "all_28_gates_pass": True, "tightest_order": tightest[1],
                     "tightest_integer_slack": tightest[0]})
    assert checks == 840
    # At received degree >= 3n/4 there is also a moment at order four.
    m = 4
    h = (3*ell-k)*m//n
    excess = 2*maximum_excess*m//n
    norm_squared = 2*m+4*excess+excess**2
    assert h == 1 and excess == 2 and norm_squared == 20
    assert 316*((h+1)//2) >= (norm_squared-1).bit_length()*(m//2)
    # The counting proof's strict margins and construction ranges.
    assert 4*A > n-1+3*(k-1)
    assert 2*A-(n-1) == 2*b+1 > ell-1
    assert A <= 3*ell-1 < 3*ell <= k+2*b < k+2*b+1 <= n-2
    assert b <= ell-1 and b+1 <= k and 2*b+1 <= k-2
    return {"prime": P, "n": n, "agreement_threshold": A,
            "received_degree_range": [A, n-2], "covered_excess_intervals": rows,
            "period_four_interval_gates": checks, "period_two_extra_gate": True,
            "written_fully_split_sublist_caps": [
                {"degree_range": [A, 3*ell-1], "cap": 3},
                {"degree_range": [3*ell, k+2*b], "cap": 1},
                {"degree_range": [k+2*b+1, n-2], "cap": 2}],
            "root_multiplicity_cap_assumed": False,
            "production_domain_enumerated": False}


def multiplicity_norm_control(v, p, z, h, excess_budget):
    n, d = len(v), len(v)//2
    actual_excess = sum(max(abs(a)-1, 0) for a in v)
    assert actual_excess <= excess_budget
    c = [v[i]-v[i+d] for i in range(d)]
    matrix = [[0]*d for _ in range(d)]
    for j in range(d):
        for i, a in enumerate(c):
            matrix[(i+j) % d][j] = a if i+j < d else -a
    det = determinant(matrix)
    zero_count = sum(sum(a*pow(z, i*j, p) for i, a in enumerate(c)) % p == 0
                     for j in range(1, n, 2))
    assert rank(matrix, p) == d-zero_count
    assert det % p**zero_count == 0
    bound = 2*n+4*excess_budget+excess_budget**2
    actual_squared_norm = sum(a*a for a in c)
    assert det**2 <= actual_squared_norm**d <= bound**d
    required = (h+1)//2
    assert all(sum(a*pow(z, i*j, p) for i, a in enumerate(c)) % p == 0
               for j in range(1, h+1, 2))
    gate = p**(2*required) > bound**d
    if gate:
        assert all(a == 0 for a in c)
    return {"indicator_excess": actual_excess, "excess_budget": excess_budget,
            "determinant": det, "primitive_zero_count": zero_count,
            "required_primitive_zeros": required, "squared_row_norm": actual_squared_norm,
            "squared_row_norm_bound": bound, "determinant_gate": gate}


def fully_split_census(p):
    """All monic split polynomials of degrees 11..14 with >=11 punctured roots.

    Enumerate each multiplicity vector by its distinct support and its extra
    copies. Group by actual coefficients; no rigidity assumption prunes this.
    """
    n = 16
    k, _, ell, A = parameters(n)
    z = root(n, p)
    factors = [(-pow(z, e, p) % p, 1) for e in range(n)]
    rows = []
    for degree in range(A, n-1):
        groups = {}
        total, nonperiodic, example = 0, 0, None
        period = 4 if degree < 3*ell else 2
        for punctured_count in range(A, min(degree, n-1)+1):
            for punctured_support in combinations(range(1, n), punctured_count):
                for includes_hole in (False, True):
                    support = ((0,)+punctured_support if includes_hole else punctured_support)
                    if len(support) > degree:
                        continue
                    base = locator(support, z, p)
                    for extra in combinations_with_replacement(support, degree-len(support)):
                        H = base
                        for e in extra:
                            H = mul(H, factors[e], p)
                        counts = Counter(support+extra)
                        multiplicities = bytes(counts[i] for i in range(n))
                        key = H[k:degree]
                        assert len(H) == degree+1 and H[-1] == 1
                        total += 1
                        if key not in groups:
                            groups[key] = [multiplicities, 1]
                            continue
                        representative, count = groups[key]
                        groups[key][1] = count+1
                        v = [a-b for a, b in zip(multiplicities, representative)]
                        assert sum(v) == 0
                        assert sum(max(abs(a)-1, 0) for a in v) <= 2*(degree-A)
                        assert all(sum(a*pow(z, i*j, p) for i, a in enumerate(v)) % p == 0
                                   for j in range(1, degree-k+1))
                        periodic = all(v[i] == v[i % period] for i in range(n))
                        nonperiodic += not periodic
                        if not periodic and example is None:
                            example = {"difference": v, "matrix_control": multiplicity_norm_control(
                                v, p, z, degree-k, 2*(degree-A))}
        histogram = Counter(group[1] for group in groups.values())
        maximum = max(histogram)
        assert sum(size*count for size, count in histogram.items()) == total
        if p == P:
            assert maximum == sublist_cap(n, degree) and nonperiodic == 0
        rows.append({"degree": degree, "enumerated_polynomials": total,
                     "coefficient_fibres": len(groups), "maximum_split_sublist": maximum,
                     "fibre_size_histogram": dict(sorted(histogram.items())),
                     "nonperiodic_differences": nonperiodic, "counterexample": example})
    assert [row['enumerated_polynomials'] for row in rows] == [1365, 16835, 112490, 539750]
    return {"n": n, "prime": p, "agreement_threshold": A, "degrees": rows}


def split_off_domain_roots(poly, n, z, p):
    """Recover multiplicities by exact synthetic division of the actual polynomial."""
    remaining = poly
    multiplicities = []
    for e in range(n):
        x, count = pow(z, e, p), 0
        while len(remaining) > 1 and evaluate(remaining, x, p) == 0:
            quotient = [0]*(len(remaining)-1)
            carry = remaining[-1]
            for j in range(len(quotient)-1, -1, -1):
                quotient[j] = carry
                carry = (remaining[j]+x*carry) % p
            assert carry == 0
            remaining = tuple(quotient)
            count += 1
        multiplicities.append(count)
    assert len(poly)-1 == sum(multiplicities)+len(remaining)-1
    return multiplicities, remaining


def sharp_constructions():
    n = 64
    k, b, ell, A = parameters(n)
    z, p = root(n, P), P
    fourth = pow(z, ell, p)
    quarters = [(-pow(fourth, j, p) % p,)+(0,)*(ell-1)+(1,) for j in (1, 2, 3)]
    halves = [(-1 % p,)+(0,)*(k-1)+(1,), (1,)+(0,)*(k-1)+(1,)]
    rows = []
    for degree in range(A, n-1):
        cap = sublist_cap(n, degree)
        if cap == 3:
            R = locator(range(4, 4*(degree-2*ell)+1, 4), z, p)
            polys = [mul(R, mul(quarters[i], quarters[j], p), p)
                     for i, j in ((0, 1), (0, 2), (1, 2))]
        elif cap == 1:
            polys = [locator(range(1, degree+1), z, p)]
        else:
            chosen = list(range(2, 2*b+1, 2))+list(range(1, 2*b+2, 2))
            chosen += [e for e in range(1, n) if e not in chosen][:degree-k-len(chosen)]
            assert len(chosen) == degree-k and len(set(chosen)) == len(chosen)
            R = locator(chosen, z, p)
            polys = [mul(R, half, p) for half in halves]
        V, values, agreements, multiplicities = polys[0], [], [], []
        for H in polys:
            f = subtract(V, H, p)
            assert len(H)-1 == degree and len(f) <= k
            support = [i for i in range(1, n) if evaluate(H, pow(z, i, p), p) == 0]
            assert len(support) >= A
            counts, outside = split_off_domain_roots(H, n, z, p)
            assert outside == (1,) and sum(counts) == degree
            assert support == [i for i in range(1, n) if counts[i]]
            multiplicities.append(counts)
            agreements.append(len(support))
            values.append(evaluate(f, 1, p))
        assert len(set(values)) == cap
        period = 4 if degree < 3*ell else 2
        for counts in multiplicities:
            v = [a-b for a, b in zip(counts, multiplicities[0])]
            assert all(v[i] == v[i % period] for i in range(n))
            assert sum(max(abs(a)-1, 0) for a in v) <= 2*(degree-A)
        rows.append({"degree": degree, "constructed_candidates": cap,
                     "distinct_values_at_hole": len(set(values)), "punctured_agreements": agreements})
    return {"n": n, "prime": P, "agreement_threshold": A, "degrees": rows,
            "completeness_is_only_within_fully_split_sublist": True}


def common_outside_factor_constructions():
    """Three candidates with the same nonconstant outside factor X^e."""
    n = 64
    k, _, ell, A = parameters(n)
    z, p = root(n, P), P
    fourth = pow(z, ell, p)
    quarters = [(-pow(fourth, j, p) % p,)+(0,)*(ell-1)+(1,) for j in (1, 2, 3)]
    rows = []
    for outside_degree in range(1, 3*ell-A):
        degree = A+outside_degree
        R = locator(range(4, 4*(A-2*ell)+1, 4), z, p)
        Q = (0,)*outside_degree+(1,)  # zero is outside mu_n
        polys = [mul(Q, mul(R, mul(quarters[i], quarters[j], p), p), p)
                 for i, j in ((0, 1), (0, 2), (1, 2))]
        V, values = polys[0], []
        for H in polys:
            assert len(H)-1 == degree
            assert all(c == 0 for c in H[:outside_degree]) and H[outside_degree] != 0
            counts, outside = split_off_domain_roots(H, n, z, p)
            assert outside == Q and sum(counts) == A
            f = subtract(V, H, p)
            assert len(f) <= k
            assert sum(evaluate(H, pow(z, i, p), p) == 0 for i in range(1, n)) == A
            values.append(evaluate(f, 1, p))
        assert len(set(values)) == 3
        rows.append({"received_degree": degree, "common_outside_factor": f"X^{outside_degree}",
                     "candidates": 3, "distinct_values": 3})
    return {"n": n, "prime": P, "examples": rows,
            "completeness_is_only_in_fixed_outside_factor_fibre": True}


def main():
    result = {"status": "PASS_SPLIT_ROOT_RIGIDITY_CONTROLS",
              "production": production_certificate(),
              "exhaustive_split_censuses": [fully_split_census(p) for p in (P, 17)],
              "sharp_constructions": sharp_constructions(),
              "common_outside_factor_constructions": common_outside_factor_constructions(),
              "Lean_formalization": False, "independent_mathematical_review": False,
              "root_escape_candidates_bounded": False, "prize_solved": False}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
