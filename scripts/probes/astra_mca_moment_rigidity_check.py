#!/usr/bin/env python3
"""Exact moment-rigidity controls; the production theorem is a written proof.

No billion-node domain or arbitrary production received word is enumerated.
"""
from collections import Counter, defaultdict
from itertools import combinations, product
import json
from math import isqrt

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478


def root(n, p):
    if p == P:
        z = pow(G, 2**30 // n, p)
    else:
        assert all(p % d for d in range(2, isqrt(p)+1))
        z = next(pow(a, (p-1)//n, p) for a in range(2, p)
                 if pow(pow(a, (p-1)//n, p), n//2, p) != 1)
    assert (p-1) % n == 0 and pow(z, n, p) == 1 and pow(z, n//2, p) != 1
    return z


def mul(a, b, p):
    out = [0]*(len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            out[i+j] = (out[i+j]+c*d) % p
    return tuple(out)


def subtract(a, b, p):
    out = [((a[i] if i < len(a) else 0)-(b[i] if i < len(b) else 0)) % p
           for i in range(max(len(a), len(b)))]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def evaluate(f, x, p):
    value = 0
    for c in reversed(f):
        value = (value*x+c) % p
    return value


def locator(exponents, z, p):
    result = (1,)
    for e in exponents:
        result = mul(result, (-pow(z, e, p) % p, 1), p)
    return result


def rank(matrix, p):
    a = [[x % p for x in row] for row in matrix]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][j], -1, p)
        a[r] = [x*inv % p for x in a[r]]
        for i in range(r+1, len(a)):
            if a[i][j]:
                c = a[i][j]
                a[i] = [(x-c*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def determinant(matrix):
    a = [row[:] for row in matrix]
    previous, sign = 1, 1
    for k in range(len(a)-1):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot_value = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = a[i][j]*pivot_value-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = pivot_value
    return sign*a[-1][-1]


def norm_control(coefficients, p, z, h):
    n, d = len(coefficients), len(coefficients)//2
    c = [coefficients[i]-coefficients[i+d] for i in range(d)]
    matrix = [[0]*d for _ in range(d)]
    for j in range(d):
        for i, a in enumerate(c):
            matrix[(i+j) % d][j] = a if i+j < d else -a
    det = determinant(matrix)
    zeros = [j for j in range(1, n, 2)
             if sum(a*pow(z, i*j, p) for i, a in enumerate(c)) % p == 0]
    assert rank(matrix, p) == d-len(zeros)
    assert det % p**len(zeros) == 0
    assert det*det <= sum(a*a for a in c)**d <= (2*n)**d
    required = (h+1)//2
    assert all(j in zeros for j in range(1, h+1, 2))
    gate = p**(2*required) > (2*n)**d
    if gate:
        assert det == 0 and all(a == 0 for a in c)
    return {"negacyclic_coefficients": c, "determinant": det,
            "primitive_zero_count": len(zeros), "required_zero_count": required,
            "squared_norm_gate": gate}


def moment_control(n, p):
    """Enumerate every signed indicator difference using two half tables."""
    z, d, h = root(n, p), n//2, (n+2)//6
    powers = [[pow(z, i*j, p) for i in range(n)] for j in range(1, h+1)]

    def key(v, offset):
        return (sum(v), *(sum(a*row[i+offset] for i, a in enumerate(v)) % p
                          for row in powers))

    first = defaultdict(list)
    for suffix in product((-1, 0, 1), repeat=d-1):
        v = (0,)+suffix  # both sets omit exponent zero
        first[key(v, 0)].append(v)
    count, nonperiodic, example = 0, 0, None
    for second in product((-1, 0, 1), repeat=d):
        k = key(second, d)
        target = (-k[0], *(-x % p for x in k[1:]))
        for left in first.get(target, ()):
            v = left+second
            assert sum(v) == 0 and v[0] == 0
            count += 1
            periodic = all(v[i] == v[i % 4] for i in range(n))
            if not periodic:
                nonperiodic += 1
                if example is None:
                    example = v
    if p in (P, 257, 1153):
        assert count == 7 and nonperiodic == 0
    result = {"n": n, "prime": p, "moments": h,
              "all_signed_vectors_covered": 3**(n-1),
              "equal_cardinality_moment_solutions": count,
              "nonperiodic_solutions": nonperiodic}
    if example is not None:
        result["counterexample"] = example
        result["norm_control"] = norm_control(example, p, z, h)
    return result


def complete_small_fibres(p):
    """All monic degree-11 divisors on the punctured order-16 domain."""
    n, k, A, h = 16, 8, 11, 3
    z = root(n, p)
    groups = defaultdict(list)
    for support in combinations(range(1, n), A):
        H = locator(support, z, p)
        groups[H[k:A]].append((set(support), H))
    maximum = max(map(len, groups.values()))
    assert sum(map(len, groups.values())) == 1365
    nonperiodic = 0
    for family in groups.values():
        support0, V = family[0]
        for support, H in family:
            difference = [int(i in support)-int(i in support0) for i in range(n)]
            assert all(sum(a*pow(z, i*j, p) for i, a in enumerate(difference)) % p == 0
                       for j in range(1, h+1))
            nonperiodic += not all(difference[i] == difference[i % 4] for i in range(n))
            f = subtract(V, H, p)
            assert len(f) <= k
            assert sum(evaluate(f, pow(z, i, p), p) == evaluate(V, pow(z, i, p), p)
                       for i in range(1, n)) == A
    if p == P:
        assert maximum == 3 and nonperiodic == 0
    return {"prime": p, "n": n, "agreement_degree": A, "divisors": 1365,
            "coefficient_fibres": len(groups), "maximum_complete_list": maximum,
            "fibre_size_histogram": dict(sorted(Counter(map(len, groups.values())).items())),
            "nonperiodic_differences_from_fibre_representatives": nonperiodic}


def sharp_control(n):
    p, z = P, root(n, P)
    ell, b, k = n//4, (n+2)//6, n//2
    A = k+b
    R = locator(range(4, 4*b+1, 4), z, p)
    fourth = pow(z, ell, p)
    private = [(-pow(fourth, j, p) % p,)+(0,)*(ell-1)+(1,) for j in (1, 2, 3)]
    H = [mul(R, mul(private[i], private[j], p), p)
         for i, j in ((0, 1), (0, 2), (1, 2))]
    V = H[0]
    values = []
    for poly in H:
        f = subtract(V, poly, p)
        assert len(V)-1 == A and len(f) <= k
        support = [i for i in range(1, n) if evaluate(poly, pow(z, i, p), p) == 0]
        assert len(support) == A
        gamma = evaluate(f, 1, p)
        assert all(evaluate(f, pow(z, i, p), p) == evaluate(V, pow(z, i, p), p)
                   for i in support)
        rows = [[pow(pow(z, i, p), j, p) for j in range(k)] for i in [0]+support]
        assert rank(rows, p) == k
        assert rank([row+[int(i == 0)] for i, row in enumerate(rows)], p) == k+1
        values.append(gamma)
    assert len(set(values)) == 3
    R1 = evaluate(R, 1, p)
    assert values == [0, -2*fourth*R1 % p, -4*fourth*R1 % p]
    return {"n": n, "prime": p, "received_degree": A, "candidate_count": 3,
            "distinct_values": values, "same_support_rank_checks": 3,
            "full_list_cap_uses_written_rigidity_proof": True}


def production_gate():
    n, h = 2**30, 178956971
    assert P == n*(2**128+192)+1
    assert pow(G, n, P) == 1 and pow(G, n//2, P) != 1
    assert P > (2*n)**4
    rows = []
    m, moments = n, h
    while m >= 8:
        r = (moments+1)//2
        assert 1 <= moments < m and 16*r >= m
        rows.append({"order": m, "moments": moments, "primitive_zeros": r,
                     "divisibility_exponent_dominates_Hadamard": 16*r >= m})
        m //= 2
        moments //= 2
    assert (m, moments) == (4, 0) and len(rows) == 28
    ell, k, A = n//4, n//2, n//2+h
    assert A == 715827883 and h <= ell-1 and A-ell < k
    return {"n": n, "prime": P, "coefficient_bound": 2,
            "sufficient_prime_lower_bound": (2*n)**4,
            "prime_gate_passes": True, "tower": rows,
            "final_period": m, "received_degree_cap": A,
            "written_complete_list_bound_in_this_class": 3,
            "production_domain_enumerated": False,
            "arbitrary_received_word_bound_proved": False}


def main():
    controls = [moment_control(n, p) for n, p in ((8, 257), (8, 17), (16, 1153), (16, P), (16, 17))]
    assert any(row['nonperiodic_solutions'] > 0 for row in controls if row['prime'] == 17)
    result = {"status": "PASS_MOMENT_RIGIDITY_CONTROLS", "signed_moments": controls,
              "complete_small_fibres": [complete_small_fibres(p) for p in (P, 17)],
              "sharp_constructions": [sharp_control(n) for n in (16, 64)],
              "production": production_gate(), "Lean_formalization": False,
              "independent_mathematical_review": False, "prize_solved": False}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
