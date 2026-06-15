#!/usr/bin/env python3
"""
wf-D2 (#444): STRUCTURE of the binding incidence I(n) — decode the closed form.

For the binding monomial direction (a,b)=(n-? , k) at the explosion size s=k+2, dump:
  - the gamma multiplicity histogram (how many witness sets R hit each distinct gamma)
  - whether gamma=0 / gamma=infinity special values dominate
  - the value 89 (n=16) decomposed against candidate closed forms.
Then sweep (a,b) to confirm the worst direction is x^k (b=k) and find a closed form for the
worst-incidence value at the explosion size across n.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from collections import Counter
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W
from probe_wf3D2_closedform_In import precompute, incidence, mono


def analyze(n, k, s, p, a, b):
    S = list(get_W(n, p).S)
    nulls = precompute(S, p, k, s)
    ua = mono(a, S, p); ub = mono(b, S, p)
    I, gammas = incidence(ua, ub, nulls, p, return_gammas=True)
    mults = sorted(gammas.values(), reverse=True)
    print(f"n={n} k={k} s={s} dir=({a},{b}) p={p}: I={I}  #witness_sets_total={len(nulls)}", flush=True)
    print(f"  gamma-mult histogram: {dict(Counter(mults))}", flush=True)
    print(f"  sum of mults = {sum(mults)} (= #far witness sets that produced a gamma)", flush=True)
    # candidate closed forms for I:
    cands = {
        '(n/2-1)^2': (n//2-1)**2,
        'C(n/2,2)': (n//2)*(n//2-1)//2,
        'n(n-1)/2 - n': n*(n-1)//2 - n,
        'C(n-1,2)': (n-1)*(n-2)//2,
        '(n/2)^2-(n/2)': (n//2)**2-(n//2),
        '6*C(n/2,2)/? ': None,
        '(n-2)(n-4)/2+1': (n-2)*(n-4)//2+1,
        'n^2/2 - 3n/2 + 1': n*n//2 - 3*n//2 + 1,
    }
    print(f"  candidate closed forms for I={I}:", flush=True)
    for name, v in cands.items():
        if v is not None:
            print(f"    {name} = {v}  {'<==MATCH' if v==I else ''}", flush=True)
    return I


if __name__ == '__main__':
    p16 = find_prime_cong1(16, 200003)
    # binding explosion at n=16: size 6, dir (10,4)
    analyze(16, 4, 6, p16, 10, 4)
    print()
    p8 = find_prime_cong1(8, 200003)
    analyze(8, 2, 4, p8, 5, 2)  # n=8 explosion at s=4 (I=9), but let's see the (5,2) dir
    print("DONE", flush=True)
