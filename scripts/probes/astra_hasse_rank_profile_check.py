#!/usr/bin/env python3
"""Exact rank profiles and positive production second-Hasse sources.

See docs/kb/astra_hasse_rank_profile-2026-09-05.md. A positive source nullity
does not establish properness of its pullback or improve the prize bound.
"""
import argparse
from functools import lru_cache
from hashlib import sha256
import json
from math import comb

from astra_c2_budget_obstruction import mixed, polarized_mixed
from astra_hasse_order_two_check import block_rank

P, N, W, A = 2130706433, 262144, 131071, 181353


@lru_cache(None)
def base_profile(h, s1, s2, prime=P):
    """Gaussian rank-profile pairs (input degree, output weight).

    Columns: (U+V-W0)^i V^j W0^k, i+j+k=h, with capped j,k.
    Rows are processed in decreasing output weight J-e; the leftmost
    nonzero column is the pivot. This reveals every required prefix rank.
    """
    columns = sorted((2*h-j-2*k, h-j-k, j, k)
                     for j in range(min(h, s1)+1)
                     for k in range(min(s2, h-j)+1))
    rows = sorted(((J-e, e, J) for e in range(h+1) for J in range(h-e+1)),
                  key=lambda row: (-row[0], row[1]))
    echelon, result = {}, []
    for weight, e, J in rows:
        values = []
        for degree, i, j, k in columns:
            u, q = J-j, i-e-(J-j)
            values.append(comb(i, e)*comb(i-e, u)*(-1)**q % prime
                          if 0 <= e <= i and u >= 0 and q >= 0 else 0)
        for column in range(len(columns)):
            if not values[column]:
                continue
            if column not in echelon:
                inverse = pow(values[column], -1, prime)
                echelon[column] = [value*inverse % prime for value in values]
                result.append((columns[column][0], weight))
                break
            scalar, previous = values[column], echelon[column]
            for j in range(column, len(columns)):
                values[j] = (values[j]-scalar*previous[j]) % prime
        if len(result) == len(columns):
            break
    # An invertible triangular variable substitution preserves independence.
    assert len(result) == len(columns)
    return tuple(result)


def shifted_profile(h, s1, s2, prime=P):
    base = min(h, s1+s2)
    shift = h-base
    return tuple((degree+2*shift, weight+shift)
                 for degree, weight in base_profile(base, s1, s2, prime))


def slices(D, w, m, s1, s2, max_h, prime=P):
    coefficients, ranks = [], []
    for h in range(max_h+1):
        cap = D-(w-2)*h
        points = shifted_profile(h, s1, s2, prime)
        coefficients.append(sum(max(0, cap-degree) for degree, weight in points))
        ranks.append(sum(max(0, min(cap, m+weight)-degree) for degree, weight in points))
    return coefficients, ranks


def profile(m, s1, s2, n=N, w=W, agreements=A, prime=P):
    assert w > 2
    D = m*agreements
    H = (D-1)//(w-2)
    coefficients, ranks = slices(D, w, m, s1, s2, H, prime)
    excess = [c-n*r for c, r in zip(coefficients, ranks)]
    slope = sum(excess)
    moment = sum(h*b for h, b in enumerate(excess))
    first = None
    running, value = 0, 0
    for T, b in enumerate(excess):
        running += b
        value += running
        if value > 0:
            first = T
            break
    if first is None and slope > 0:
        first = max(H, moment//slope)
    return {"m":m,"s1":s1,"s2":s2,"H":H,"slope":slope,
            "moment":moment,"first_T":first}, coefficients, ranks


def source(m, s1, s2, expected_T, expected_margin):
    row, cs, rs = profile(m, s1, s2)
    T = row["first_T"]
    assert T == expected_T and T >= row["H"]
    C = sum((T+1-h)*c for h, c in enumerate(cs))
    R = sum((T+1-h)*r for h, r in enumerate(rs))
    margin = C-N*R
    assert margin == expected_margin > 0
    assert T*row["slope"]-row["moment"] <= 0
    # Conditional degree bookkeeping after Y2=G/(2H) at the binding flag.
    Rcap = s1+11*s2
    Ycap = row["H"]+46*s2
    Tcap = T+2363*s2
    cut = (Tcap-Ycap, Ycap-Rcap, Rcap)
    first_tail = (2*2317*(W+1), 1+2*37*(W+1), 2*9*(W+1))
    cost = mixed((2317,37,10), first_tail, cut)
    assert cost == polarized_mixed((2317,37,10), first_tail, cut)
    return dict(row, D=m*A, coefficients=C, exact_single_node_rank=R,
                guaranteed_kernel_dimension=margin,
                cleared_cut_raw_flag=cut, conditional_proper_cut_mixed_cost=cost,
                properness_proved=False)


def comparisons():
    count = 0
    for prime in (2,5,17,P):
        for s1,s2 in ((0,1),(1,1),(2,1),(2,2),(3,2)):
            for h in range(8):
                direct = base_profile(h,s1,s2,prime)
                shifted = shifted_profile(h,s1,s2,prime)
                for m in (1,2,4,7):
                    for r in range(m+h):
                        expected = block_rank(h,r,m,s1,s2,prime)
                        assert sum(d <= r < m+v for d,v in direct) == expected
                        assert sum(d <= r < m+v for d,v in shifted) == expected
                        count += 1
    # Nontrivial production-sized blocks, compared to the older sparse expansion.
    large = []
    m,s1,s2 = 80,24,6
    for h in (12,24,30,64,100,110):
        points = shifted_profile(h,s1,s2)
        candidates = [(r,sum(d <= r < m+v for d,v in points)) for r in range(m+h)]
        candidates = [(r,rank) for r,rank in candidates if 0 < rank < len(points)]
        if not candidates:
            continue
        for index in sorted({0,len(candidates)//3,2*len(candidates)//3,len(candidates)-1}):
            r, rank = candidates[index]
            assert block_rank(h,r,m,s1,s2,P) == rank
            large.append({"h":h,"r":r,"rank":rank})
    return count, large


def reproduce_small_exclusion():
    rows = []
    for m in range(1,25):
        for s1 in range(min(12,m)+1):
            for s2 in range(1,min(6,m)+1):
                row, _, _ = profile(m,s1,s2)
                assert row["slope"] < 0 and row["first_T"] is None
                rows.append(row)
    digest = sha256(json.dumps(rows,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    assert len(rows) == 1426
    assert digest == "e3236262b641883c85187739a7363344cf1902105a56bf67454df7ee202347e2"
    return {"profiles":len(rows),"digest":digest}


def scan():
    rows = []
    for s1 in (8,12,18,24,30,36,42,51):
        for s2 in (1,2,4,6,8,12):
            for m in (32,48,64,80,99,120,144,166,200,240,270):
                row, _, _ = profile(m,s1,s2)
                rows.append(row)
    passed = [row for row in rows if row["first_T"] is not None]
    assert len(rows) == 528
    digest = sha256(json.dumps(rows,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    assert len(passed) == 123
    assert digest == "3716560c6d39d65ae32673385d63ff1149f6bd3e16cb8ee6e4528f252fb59966"
    return {"profiles":len(rows),"positive_profiles":len(passed),
            "smallest_T_rows":sorted(passed,key=lambda row:row["first_T"])[:10],
            "digest":digest}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan",action="store_true",help="also reproduce the 528-profile bounded search")
    args = parser.parse_args()
    small, large = comparisons()
    exclusion = reproduce_small_exclusion()
    sources = [source(*row) for row in ((80,24,6,1042,653072574),
               (99,30,8,1031,1789994979),(99,30,1,4156,69165548),
               (99,30,2,2270,215109102))]
    old80, _, _ = profile(80,24,0)
    old99, _, _ = profile(99,30,0)
    old166, _, _ = profile(166,51,0)
    assert old80["slope"] == -22039275 and old80["first_T"] is None
    assert old99["first_T"] == 217071 and old166["first_T"] == 7159
    assert 7160*old166["slope"]-old166["moment"] == 228451639
    output = {"status":"PASS_PRODUCTION_SECOND_HASSE_DIMENSION_CERTIFICATES",
              "field_characteristic":P,"n":N,"degree_bound":W,"agreement_target":A,
              "small_block_comparisons":small,"production_block_comparisons":large,
              "reproduced_prior_exclusion":exclusion,"sources":sources,
              "order_one_controls":[old80,old99,old166],
              "full_production_global_matrix_constructed":False,
              "lean_run_performed":False,"prize_bound_improved":False}
    if args.scan:
        output["bounded_scan"] = scan()
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
