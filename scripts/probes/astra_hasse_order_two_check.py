#!/usr/bin/env python3
"""Exact finite Hasse-order-two local ranks; no production list bound."""

from functools import lru_cache
from math import comb, isqrt
import json

P = 2130706433


def sparse_rank(columns, prime):
    pivots = {}
    for source in columns:
        column = {key: value % prime for key, value in source.items() if value % prime}
        while column:
            pivot = min(column)
            if pivot not in pivots:
                inverse = pow(column[pivot], -1, prime)
                pivots[pivot] = {key: value*inverse % prime for key, value in column.items()}
                break
            scalar = column[pivot]
            for key, value in pivots[pivot].items():
                updated = (column.get(key, 0)-scalar*value) % prime
                if updated:
                    column[key] = updated
                else:
                    column.pop(key, None)
    return len(pivots)


@lru_cache(None)
def block_rank(h, r, m, s1, s2, prime):
    columns = []
    for i in range(h+1):
        for j in range(min(s1, h-i)+1):
            k, a = h-i-j, r-2*i-j
            if k > s2 or a < 0 or a+i >= m:
                continue
            column = {}
            for e in range(i+1):
                for v in range(i-e+1):
                    u = i-e-v
                    t = a+u+2*v
                    if t+3*e < m:
                        column[e, j+u] = comb(i, e)*comb(i-e, v)*(-1)**v
            columns.append(column)
    return sparse_rank(columns, prime)


def coefficients(D, w, T, s1, s2):
    return sum((T+1-i-j-k)*max(0, D-w*i-(w-1)*j-(w-2)*k)
               for i in range(T+1)
               for j in range(min(s1, T-i)+1)
               for k in range(min(s2, T-i-j)+1))


def rank_two(D, w, T, m, s1, s2, prime=P):
    return sum((T+1-h)*block_rank(h, r, m, s1, s2, prime)
               for h in range(T+1) for r in range(m+h)
               if r+(w-2)*h < D)


def rank_one(D, w, T, m, s1):
    return sum((T+1-h)*min(max(0, min(h, r)-max(0, h-s1)+1), m-r)
               for h in range(T+1) for r in range(m)
               if r+(w-1)*h < D)


def dense_rank(rows, prime):
    rows = [[value % prime for value in row] for row in rows]
    rank = 0
    for column in range(len(rows[0]) if rows else 0):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        inverse = pow(rows[rank][column], -1, prime)
        rows[rank] = [value*inverse % prime for value in rows[rank]]
        for i in range(rank+1, len(rows)):
            scalar = rows[i][column]
            rows[i] = [(a-scalar*b) % prime for a, b in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def direct_rank(D, w, T, m, s1, s2, prime, node, u0, u1, order):
    # Independent full monomial substitution at a non-centered received point.
    # Row exponents are (t,v,Y1,Y2,Z); weight(v)=order+1.
    zero = (0, 0, 0, 0, 0)
    terms = {zero: u0, (0, 0, 0, 0, 1): u1, (1, 0, 1, 0, 0): 1,
             (0, 1, 0, 0, 0): 1}
    if order == 2:
        terms[2, 0, 0, 1, 0] = -1
    powers = [{zero: 1}]
    for _ in range(T):
        following = {}
        for a, ca in powers[-1].items():
            for b, cb in terms.items():
                key = tuple(x+y for x, y in zip(a, b))
                if key[0]+(order+1)*key[1] < m:
                    following[key] = (following.get(key, 0)+ca*cb) % prime
        powers.append({key: value for key, value in following.items() if value})
    columns = []
    for i in range(T+1):
        for j in range(min(s1, T-i)+1):
            for k in range(min(s2, T-i-j)+1):
                width = max(0, D-w*i-(w-1)*j-(w-2)*k)
                for z in range(T+1-i-j-k):
                    for x in range(width):
                        column = {}
                        for a in range(min(x, m-1)+1):
                            scalar = comb(x, a)*pow(node, x-a, prime)
                            for (t, e, J, K, Z), value in powers[i].items():
                                if t+a+(order+1)*e < m:
                                    key = t+a, e, J+j, K+k, Z+z
                                    column[key] = (column.get(key, 0)+scalar*value) % prime
                        columns.append(column)
    assert len(columns) == coefficients(D, w, T, s1, s2)
    keys = sorted({key for column in columns for key in column})
    return dense_rank([[column.get(key, 0) for column in columns] for key in keys], prime)


def small_checks():
    checks = 0
    for prime in (2, 5, P):
        for D, w, T, m, s1, s2 in ((9, 2, 2, 4, 1, 1), (15, 3, 3, 3, 2, 1),
                                   (19, 4, 3, 5, 3, 2)):
            for node, u0, u1 in ((0, 0, 0), (2, 3, 4)):
                assert direct_rank(D, w, T, m, s1, s2, prime, node, u0, u1, 2) == \
                    rank_two(D, w, T, m, s1, s2, prime)
                assert direct_rank(D, w, T, m, s1, 0, prime, node, u0, u1, 1) == \
                    rank_one(D, w, T, m, s1)
                assert rank_two(D, w, T, m, s1, 0, prime) == rank_one(D, w, T, m, s1)
                checks += 2
        # Monomial Taylor checks use Hasse binomial coefficients, never f''/2.
        for degree in range(10):
            for t in (1, 2):
                coefficient = (comb(degree, t) if t <= degree else 0)
                coefficient -= degree*(comb(degree-1, t-1) if degree >= t else 0)
                coefficient += (comb(degree, 2)*comb(degree-2, t-2)
                                if degree >= t >= 2 else 0)
                assert coefficient % prime == 0
    return checks


def comparison(n, w, A):
    m, T, s1, s2 = 8, 16, 4, 2
    D = m*A
    C1, C2 = coefficients(D, w, T, s1, 0), coefficients(D, w, T, s1, s2)
    L1, L2 = rank_one(D, w, T, m, s1), rank_two(D, w, T, m, s1, s2)
    return {'n': n, 'message_degree_at_most': w, 'agreements': A, 'multiplicity': m,
            'D': D, 'T': T, 'Y1_cap': s1, 'Y2_cap': s2,
            'order_one': {'coefficients': C1, 'local_rank': L1, 'nullity_lower': C1-n*L1},
            'order_two': {'coefficients': C2, 'local_rank': L2, 'nullity_lower': C2-n*L2}}


def main():
    assert all(P % divisor for divisor in range(2, isqrt(P)+1))
    assert (P-1) % 64 == 0
    direct_checks = small_checks()
    positive = comparison(64, 15, 34)
    assert positive['order_one'] == {'coefficients': 106665, 'local_rank': 1690,
                                     'nullity_lower': -1495}
    assert positive['order_two'] == {'coefficients': 269845, 'local_rank': 4162,
                                     'nullity_lower': 3477}
    # Exact finite threshold comparison: m=8,T=16 fixed throughout. For order
    # one, test every separate Y1 cap 0..16, not only the displayed cap four.
    for A in range(1, 35):
        assert all(coefficients(8*A, 15, 16, s, 0) <=
                   64*rank_one(8*A, 15, 16, 8, s) for s in range(17))
    for A in range(1, 34):
        assert coefficients(8*A, 15, 16, 4, 2) <= 64*rank_two(8*A, 15, 16, 8, 4, 2)
    assert comparison(64, 15, 35)['order_one']['nullity_lower'] == 3345
    production = comparison(262144, 131071, 181353)
    assert production['order_two'] == {'coefficients': 898433625, 'local_rank': 4143,
                                       'nullity_lower': -187628967}
    assert production['order_one']['nullity_lower'] == -58123765
    print(json.dumps({'status': 'PASS_EXACT_HASSE_ORDER_TWO_FINITE_INTERPOLATION',
                      'prime': P, 'valid_over_extensions': True,
                      'independent_direct_local_matrices_checked': direct_checks,
                      'finite_gain': positive,
                      'first_positive_order_one_among_17_slope_caps': 35,
                      'first_positive_order_two_fixed_box': 34,
                      'production_same_small_box': production,
                      'production_or_list_bound_proved': False}, sort_keys=True))


if __name__ == '__main__':
    main()
