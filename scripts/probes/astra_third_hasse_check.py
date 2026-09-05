#!/usr/bin/env python3
"""Check third-Hasse rank profiles; positive nullity does not prove properness."""
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import tempfile

from astra_hasse_order_two_check import sparse_rank
from astra_hasse_rank_profile_check import profile as second_profile

P, N, W, A = 2130706433, 262144, 131071, 181353


def direct_block(h, r, m, caps, p):
    """Expand X^a Y^i R1^j R2^k R3^l after the original substitution.

    Row keys are literal (t,v,R1,R2,R3) exponents, not rank-profile weights.
    """
    columns = []
    for j, k, l in product(*(range(s+1) for s in caps)):
        i = h-j-k-l
        a = r-3*h+j+2*k+3*l
        if i < 0 or a < 0:
            continue
        column = {}
        for v in range(i+1):
            for u1 in range(i-v+1):
                for u2 in range(i-v-u1+1):
                    u3 = i-v-u1-u2
                    t = a+u1+2*u2+3*u3
                    if t+4*v >= m:
                        continue
                    value = comb(i, v)*comb(i-v, u1)*comb(i-v-u1, u2)*(-1)**u2 % p
                    if value:
                        column[t, v, j+u1, k+u2, l+u3] = value
        columns.append(column)
    return sparse_rank(columns, p)


def invoke(binary, *args):
    run = subprocess.run([str(binary), *map(str, args)], check=True,
                         capture_output=True, text=True)
    assert not run.stderr
    return json.loads(run.stdout)


def finite_controls(binary):
    cases = 0
    shifts = 0
    for p in (2, 5, 17, P):
        for caps in ((0, 0, 0), (1, 1, 0), (1, 1, 1), (2, 1, 1), (2, 2, 1)):
            profiles = {}
            for h in range(7):
                points = invoke(binary, 'profile', h, *caps, p)
                profiles[h] = points
                b = min(h, sum(caps))
                shifted = [(d+3*(h-b), v+2*(h-b)) for d, v in profiles[b]]
                for m in (1, 2, 4, 7):
                    for r in range(3*h+m):
                        rank = sum(d <= r < m+v for d, v in points)
                        assert rank == direct_block(h, r, m, caps, p)
                        assert rank == sum(d <= r < m+v for d, v in shifted)
                        cases += 1
                shifts += h > b
    return {"direct_block_comparisons": cases, "shifted_degree_profiles": shifts}


def source_coefficients(D, T, caps):
    """Independent source summation in the original monomial exponents."""
    total = 0
    for j, k, l in product(*(range(s+1) for s in caps)):
        width = D-(W-1)*j-(W-2)*k-(W-3)*l
        for i in range(max(0, (width-1)//W+1)):
            copies = T-i-j-k-l+1
            if copies > 0:
                total += copies*(width-W*i)
    return total


def production_controls(binary):
    # The zero-R3 source must reproduce the independently implemented order-two profile.
    baseline = invoke(binary, 80, 24, 6, 0)
    old, cs, rs = second_profile(80, 24, 6)
    assert baseline['T'] == old['first_T'] == 1042
    assert baseline['coefficients'] == sum((1043-h)*c for h, c in enumerate(cs))
    assert baseline['single_node_rank'] == sum((1043-h)*r for h, r in enumerate(rs))
    assert baseline['margin'] == 653072574
    rows = []
    for params, expected in (
            ((80, 24, 6, 1), (925, 185934664372800, 709277398, 1850151488)),
            ((99, 30, 8, 1), (915, 439776945574395, 1677611971, 1033048571)),
            ((80, 24, 6, 2), (992, 296942308628000, 1132736412, 2254640672))):
        row = invoke(binary, *params)
        T, C, L, margin = expected
        assert (row['T'], row['coefficients'], row['single_node_rank'], row['margin']) == expected
        assert C-N*L == margin > 0
        assert row['D'] == params[0]*A < P
        assert C == source_coefficients(row['D'], T, params[1:])
        assert row['H'] <= T and row['slope'] > 0
        assert T*row['slope']-row['moment'] <= 0
        assert (T+1)*row['slope']-row['moment'] == margin
        exponent = params[2]+3*params[3]
        cut = T+2363*exponent
        row.update(denominator_exponent=exponent, cleared_total_cap=cut,
                   conditional_component_allowance=188834222914524+2951611603152*cut,
                   properness_proved=False)
        rows.append(row)
    rejected = 0
    for args in ((), ('0','1','1','1'), ('80x','1','1','1'),
                 ('80','24','6','4'), ('profile','3','1','1','1','4')):
        run = subprocess.run([str(binary), *args], capture_output=True, text=True)
        assert run.returncode != 0 and 'third-Hasse profile error:' in run.stderr
        rejected += 1
    return {"order_two_reproduction": baseline, "third_order_sources": rows,
            "malformed_arguments_rejected": rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sanitize', action='store_true')
    args = parser.parse_args()
    compiler = shutil.which('clang++') or shutil.which('g++')
    if not compiler:
        raise RuntimeError('C++17 compiler required')
    with tempfile.TemporaryDirectory(prefix='astra-third-hasse-') as folder:
        binary = Path(folder)/'profile'
        flags = ['-O1', '-fsanitize=undefined', '-fno-sanitize-recover=all'] if args.sanitize else ['-O3']
        subprocess.run([compiler, *flags, '-std=c++17', str(Path(__file__).with_name(
            'astra_third_hasse_profile.cpp')), '-o', str(binary)], check=True)
        output = {"status": "PASS_THIRD_HASSE_DIMENSION_CONTROLS",
                  "finite": finite_controls(binary),
                  "production": production_controls(binary),
                  "sanitized": args.sanitize,
                  "full_global_kernel_constructed": False,
                  "independent_mathematical_review": False,
                  "Lean_formalization": False, "prize_bound_improved": False}
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
