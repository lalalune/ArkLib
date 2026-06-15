#!/usr/bin/env python3
"""
wf-D2 (#444): n=32 binding s* and explosion value at the WORST monomial direction only.

Full a-sweep is infeasible at n=32 (C(32,s) precompute). The worst far direction is empirically
b=k (lowest far exponent) with a small set of a. We compute I(a,b;s) over a focused (a,b) grid at
each binding size and report s* (largest good, I<=budget=n) and the explosion value I(n).

Vectorized incidence: precompute left-null vectors once per size; reuse across directions.
"""
import sys, itertools, argparse
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W
from probe_wf3D2_closedform_In import left_null_rows, mono


def precompute(S, p, k, s, cap=None):
    n = len(S); res = []; cnt = 0
    for R in itertools.combinations(range(n), s):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null_rows(V, p)
        if P:
            res.append((R, P)); cnt += 1
            if cap and cnt >= cap:
                break
    return res


def inc(u0, u1, nulls, p):
    good = set()
    for R, P in nulls:
        sz = len(R)
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return p
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good.add(g)
    return len(good)


def run(n, k, smin, smax, p, dirs):
    S = list(get_W(n, p).S)
    budget = n
    print(f"n={n} k={k} rho={k/n} budget={budget} p={p} dirs={dirs}", flush=True)
    print(f"{'s':>3} {'r':>3} {'maxI':>8} {'best_dir':>10}", flush=True)
    last_good = None; explosion = None
    for s in range(smax, smin - 1, -1):
        nulls = precompute(S, p, k, s)
        best = (-1, None)
        for (a, b) in dirs:
            if a == b: continue
            I = inc(mono(a, S, p), mono(b, S, p), nulls, p)
            if p > I > best[0]:
                best = (I, (a, b))
        print(f"{s:>3} {n-s:>3} {best[0]:>8} {str(best[1]):>10}", flush=True)
        if best[0] <= budget:
            last_good = (s, n - s)
        elif last_good is not None and explosion is None:
            explosion = best[0]
    if last_good:
        ss, rr = last_good
        print(f"\n*** s*={ss} r*={rr} delta*={rr}/{n}={rr/n:.4f}  explosion I(n)={explosion}", flush=True)
    print("DONE", flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--smin', type=int, required=True)
    ap.add_argument('--smax', type=int, required=True)
    ap.add_argument('--prime', type=int, default=200003)
    args = ap.parse_args()
    p = find_prime_cong1(args.n, args.prime)
    n, k = args.n, args.k
    # focused worst-direction grid: b=k (lowest far), and a few low far b; a near n-2..n and a small.
    dirs = []
    for b in (k, k+1, k+2):
        for a in list(range(n)):
            dirs.append((a, b))
    run(n, k, args.smin, args.smax, p, dirs)
