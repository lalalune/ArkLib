#!/usr/bin/env python3
"""Contact-loss controls and the analytic tail of the low-R margin exclusion.

The finite first-order audit is separate: astra_root_safe_filtration.cpp.
No actual-kernel nonexistence, general properness, or prize bound is claimed.
"""
import json
from itertools import product
from math import comb, isqrt

from astra_hasse_order_two_check import dense_rank
from astra_positive_kernel_factor_check import kernel

N, W, A = 262144, 131071, 181353


def ordinary_counts(D, w, T, m):
    if D <= 0 or T < 0:
        return 0, 0
    C = L = 0
    for j in range(T+1):
        length = max(0, D-w*j)
        C += (T+1-j)*length
        L += (T+1-j)*max(0, min(length, m-j))
    return C, L


def ordinary_controls():
    count = 0
    for w in (3, 5, 8):
        for n in (2*w, 3*w, 4*w):
            B = isqrt(n*w)
            delta = n*w-B*B
            kappa = delta+w*(n-B)-w*w//4
            assert w < B < n and kappa > 0
            for m in range(1, 9):
                Dmax = m*B
                q, remainder = divmod(Dmax, w)
                Cstar = sum(max(0, Dmax-w*j) for j in range(q+1))
                gap = n*m*(m+1)//2-Cstar
                assert 2*w*gap == m*m*delta+m*w*(n-B)-remainder*(w-remainder)
                assert 2*w*gap >= kappa > 0
                for D in range(1, Dmax+1):
                    H = (D-1)//w
                    for T in range(H+4):
                        C, L = ordinary_counts(D, w, T, m)
                        assert C-n*L < 0
                        count += 1
                    # The remaining tail is affine; check its slope separately.
                    c0, l0 = ordinary_counts(D, w, H+2, m)
                    c1, l1 = ordinary_counts(D, w, H+3, m)
                    assert c1-c0-n*(l1-l0) < 0
            assert ordinary_counts(n+1, w, 0, 1)[0]-n == 1
    return count


def monomials(D, w, T, caps):
    out = []
    for jets in product(*(range(cap+1) for cap in caps)):
        for y in range(T-sum(jets)+1):
            for z in range(T-sum(jets)-y+1):
                limit = D-w*y-sum((w-j)*e for j, e in enumerate(jets, 1))
                out.extend((x, y)+jets+(z,) for x in range(max(0, limit)))
    return out


def contact_column(mon, order, m, p, node, u0, u1):
    x, y, *rest = mon
    jets, z = rest[:-1], rest[-1]
    zero = (0,)*(order+3)  # t,v,R1,...,Rd,Z
    terms = {zero: u0}
    key = list(zero)
    key[-1] = 1
    terms[tuple(key)] = u1
    key = list(zero)
    key[1] = 1
    terms[tuple(key)] = 1
    for j in range(1, order+1):
        key = list(zero)
        key[0], key[1+j] = j, 1
        terms[tuple(key)] = (-1)**(j+1)
    power = {zero: 1}
    for _ in range(y):
        result = {}
        for left, a in power.items():
            for right, b in terms.items():
                key = tuple(i+j for i, j in zip(left, right))
                if key[0]+(order+1)*key[1] < m:
                    result[key] = (result.get(key, 0)+a*b) % p
        power = {key: value for key, value in result.items() if value}
    out = {}
    for k in range(min(x, m-1)+1):
        scalar = comb(x, k)*pow(node, x-k, p) % p
        for key, value in power.items():
            key = list(key)
            key[0] += k
            if key[0]+(order+1)*key[1] >= m:
                continue
            for j, exponent in enumerate(jets):
                key[2+j] += exponent
            key[-1] += z
            key = tuple(key)
            out[key] = (out.get(key, 0)+scalar*value) % p
    return {key: value for key, value in out.items() if value}


def ordinary_column(mon, m, p, node, u0, u1):
    x, y, *rest = mon
    jets, z = tuple(rest[:-1]), rest[-1]
    out = {}
    for k in range(min(x, m-1)+1):
        scalar = comb(x, k)*pow(node, x-k, p) % p
        for v in range(min(y, m-k-1)+1):
            for zz in range(y-v+1):
                value = (scalar*comb(y, v)*comb(y-v, zz)*pow(u0, y-v-zz, p)
                         *pow(u1, zz, p)) % p
                if value:
                    out[jets+(k, v, z+zz)] = value
    return out


def rows(columns):
    keys = sorted({key for column in columns for key in column})
    return [[column.get(key, 0) for column in columns] for key in keys]


def contact_controls():
    receipts = []
    for p in (2, 5, 17, 2130706433):
        for order, r in ((1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)):
            m, w, T = order*r+2, order+2, 2
            D = 2*m+w
            caps = (r,)+(1,)*(order-1)
            mons = monomials(D, w, T, caps)
            node, u0, u1 = 1, 1, 1
            actual = rows([contact_column(mon, order, m, p, node, u0, u1) for mon in mons])
            coefficient = rows([ordinary_column(mon, m-order*r, p, node, u0, u1) for mon in mons])
            rank, vectors = kernel(actual, p)
            # Every extracted coefficient of every full local-kernel vector
            # satisfies ordinary contact at least m-order*r.
            for vector in vectors:
                assert all(sum(a*b for a, b in zip(row, vector)) % p == 0 for row in coefficient)
            expected = sum(ordinary_counts(
                D-sum((w-j)*e for j, e in enumerate(jets, 1)), w, T-sum(jets), m-order*r)[1]
                for jets in product(*(range(cap+1) for cap in caps)))
            coefficient_rank = dense_rank(coefficient, p)
            assert coefficient_rank == expected <= rank
            if r == 0:
                assert coefficient_rank == rank
            receipts.append({"p": p, "order": order, "R_cap": r, "m": m,
                             "columns": len(mons), "contact_rank": rank,
                             "ordinary_coefficient_rank": coefficient_rank,
                             "kernel_vectors_checked": len(vectors)})
    # Coefficient extraction uses Hasse derivatives, including at small characteristic.
    identities = 0
    for p in (2, 3, 5, 17, 2130706433):
        for degree in range(13):
            for i in range(degree+1):
                value = sum((-1)**(j-i)*comb(j, i)*comb(degree, j)
                            for j in range(i, degree+1)) % p
                assert value == int(degree == i)
                identities += 1
    return receipts, identities


def main():
    B = isqrt(N*W)
    delta = N*W-B*B
    kappa = delta+W*(N-B)-W*W//4
    assert (B, B-A, delta, kappa) == (185363, 4010, 34455, 5768895146)
    cutoffs = []
    for order in (1, 2, 3):
        for r in range(10):
            threshold = (order*r*B+B-A-1)//(B-A)
            assert threshold*(B-A) >= order*r*B
            if threshold:
                assert (threshold-1)*(B-A) < order*r*B
            if order == 1:
                assert threshold <= 417 < 500
            cutoffs.append({"order": order, "R_cap": r, "m_at_least": max(1, threshold)})
    local, identities = contact_controls()
    print(json.dumps({"status": "PASS_CONTACT_LOSS_AND_ANALYTIC_MARGIN_TAIL",
                      "ordinary_count_controls": ordinary_controls(), "contact_controls": local,
                      "Hasse_coefficient_identities": identities, "production_B": B,
                      "production_rounding_certificate": kappa, "cutoffs": cutoffs,
                      "finite_first_order_audit_required_separately": {
                          "source": "scripts/probes/astra_root_safe_filtration.cpp",
                          "max_m": 500, "max_R_cap": 9},
                      "actual_kernels_excluded": False, "production_properness_proved": False,
                      "prize_bound_improved": False, "independent_review_and_Lean_complete": False},
                     sort_keys=True))


if __name__ == "__main__":
    main()
