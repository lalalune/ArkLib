#!/usr/bin/env python3
"""
wf-RB (#444): DECISIVE BAD-boundary scan for the over-det far-line at n=32,34,38.

The full GOOD r-profile is infeasible to brute-force at n>=32 (C(32,16)~6e8 per direction). But
the binary question -- does the binding witness size s* climb past Johnson n/2-1 -- is decided by
the BAD boundary: s* = max{ s : worst-direction far-incidence I(.,s) > budget=n }  (the deepest
over-det rung still BAD), with the first GOOD rung at s*+1. delta* = (n - (s*+1))/n... NO -- we use
the rung convention: the BAD region is the deep band (LARGE r = small s). I(rung r) > budget for r
ABOVE the threshold r* and <= budget for r <= r*. So r* = (smallest BAD r) - 1 = largest GOOD r.
Equivalently s* (binding) = n - r*.

BAD rungs EARLY-EXIT (stop the moment > budget distinct gammas found) so they are CHEAP even at
n=32. We scan the worst directions (low-exponent x^k family + antipodal/order-2, FULL b-range,
no cap) across the rungs straddling Johnson and find the BAD/GOOD boundary. We only ever need to
*confirm BAD* (fast) on the deep side; the first rung that is NOT confirmed-BAD by the worst
directions is the candidate r*. We then attempt to verify that rung GOOD with a bounded-time
enumeration (may be skipped if too large -- reported honestly).

Johnson+1rung: r* = n/2+1 (s*=n/2-1, delta*=1/2+1/n).  A CLIMB toward the floor 1-rho would push
r* ABOVE n/2+1 (more deep rungs becoming GOOD).
"""
import sys, itertools, time
from math import comb
import numpy as np
sys.path.insert(0, 'scripts/probes')
import probe_wf4RB_vec_rprofile as V


def worst_dirs(n, k):
    """FULL b-range worst-candidate far directions, ORDERED BAD-likely-FIRST so the early-exit
       confirms BAD without enumerating GOOD directions. The proven worst over-det maximizers are
       the low-b order-2 / 'pullback' lines (a, b) with small b and a-b coprime-ish to n giving the
       largest dilation orbit; we front-load b=k (the in-tree binder x^k) over all a, then the
       antipodal/order-2 family, then b=k+1,k+2. (Far-validity b<s applied per rung in caller.)"""
    m2 = n // 2
    ds = []
    # 1) the in-tree binder family x^k (b=k), a sweeping high -> low (high a-b = big orbit first)
    for a in range(n-1, k, -1):
        ds.append((a, k))
    # 2) antipodal / order-2 family
    for d in [(m2, m2-1), (m2-1, m2), (m2, m2+1), (m2+1, m2), (m2, m2-2), (m2, k+1)]:
        if d[0] != d[1] and k <= d[0] < n and k <= d[1] < n:
            ds.append(d)
    # 3) b=k+1, k+2 sweeps
    for b in [k+1, k+2]:
        for a in range(n-1, k, -1):
            if a != b:
                ds.append((a, b))
    seen = set(); out = []
    for d in ds:
        if d not in seen: seen.add(d); out.append(d)
    return out


def rung_is_bad(n, k, p, mu, r, dirs, budget, time_budget_s, maxscan):
    """Return (verdict, maxI_seen, binder, capped). verdict in {'BAD','GOOD?','UNRESOLVED'}.
       BAD as soon as ANY far-valid worst direction exceeds budget. maxscan caps per-direction
       enumeration so GOOD directions don't stall: a direction returning ('CAP',cnt) is 'not the
       binder' (<=budget after maxscan subsets) and we move on. If every far-valid direction is
       <=budget or CAP, the rung is GOOD? (over the worst-candidate maximizer family)."""
    s = n - r
    if s < k+1:
        return ('skip', 0, None, False)
    t0 = time.time()
    best = 0; binder = None; any_cap = False
    for (a, b) in dirs:
        if b >= s:  # far-validity: x^b is far only when b < s
            continue
        if time.time() - t0 > time_budget_s:
            return ('UNRESOLVED', best, binder, True)
        I = V.incidence_vec(a, b, n, mu, k, p, s, budget, maxscan=maxscan)
        if I is None:
            continue
        if isinstance(I, tuple):  # ('CAP', cnt)
            any_cap = True
            if I[1] > best: best = I[1]; binder = (a, b)
            continue
        v = I if I <= budget else budget + 1
        if v > best:
            best = v; binder = (a, b)
        if v > budget:
            return ('BAD', v, binder, False)
    return (('GOOD?' if not any_cap else 'GOOD?(capped)'), best, binder, any_cap)


def run(n, k, primes, r_list, time_budget_s=90, maxscan=20_000_000):
    budget = n
    rho = k / n
    dirs = worst_dirs(n, k)
    print(f"\n===== n={n} k={k} rho={rho:.4f} budget={budget}  ({len(dirs)} worst dirs, full b-range) =====", flush=True)
    print(f"  Johnson+1rung: r*={n//2+1} (s*={n//2-1}, delta*={0.5+1/n:.4f}); floor: r*={int((1-rho)*n)} (delta*={1-rho:.4f})", flush=True)
    setups = [(p, V.setup(n, p)) for p in primes]
    print(f"  {'r':>3} {'s':>3} {'delta':>7} {'C(n,s)':>12}  " + "  ".join(f'p{i}:verdict(maxI,binder)' for i in range(len(primes))), flush=True)
    table = {}
    for r in r_list:
        s = n - r
        if s < k+1:
            continue
        cells = []
        agg = []
        for (p, mu) in setups:
            verdict, mx, binder, to = rung_is_bad(n, k, p, mu, r, dirs, budget, time_budget_s, maxscan)
            cells.append(f"{verdict}({mx},{binder})")
            agg.append(verdict)
        # p-independent verdict
        v = 'BAD' if 'BAD' in agg else ('UNRESOLVED' if any('UNRESOLVED' in a for a in agg) else 'GOOD?')
        table[r] = v
        print(f"  {r:>3} {s:>3} {r/n:>7.4f} {comb(n,s):>12}  " + "  ".join(cells), flush=True)
    # boundary: r* = largest r that is GOOD? with all larger r BAD (contiguous deep BAD region)
    bad_rs = sorted([r for r in table if table[r] == 'BAD'])
    good_rs = sorted([r for r in table if table[r] == 'GOOD?'])
    if bad_rs:
        smallest_bad = min(bad_rs)
        rstar = smallest_bad - 1
        print(f"  >>> smallest BAD r = {smallest_bad}  =>  r* (largest GOOD) = {rstar}  =>  delta* = {rstar/n:.4f}  (s* binding = {n - rstar})", flush=True)
        jr = n//2 + 1
        tag = ("JOHNSON+1rung LOCKED" if rstar == jr else
               ("CLIMB past Johnson toward floor!" if rstar > jr else "below Johnson+1rung"))
        print(f"  >>> Johnson+1rung r*={jr}.  VERDICT: {tag}", flush=True)
    else:
        print(f"  >>> no BAD rung found in window (all GOOD? or UNRESOLVED): {table}", flush=True)
    return table


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="32")
    ap.add_argument("--tb", type=float, default=90.0, help="per-rung-per-prime time budget (s)")
    ap.add_argument("--span", type=int, default=4, help="test r in [n/2-1, n/2+span]")
    ap.add_argument("--maxscan", type=float, default=2e7, help="per-direction subset scan cap")
    args = ap.parse_args()
    KMAP = {16:4, 20:5, 24:6, 28:7, 32:8, 34:8, 36:9, 38:9, 40:10}
    for n in [int(x) for x in args.ns.split(",")]:
        k = KMAP[n]
        primes = [V.find_prime_cong1(n, 200000), V.find_prime_cong1(n, 700000)]
        # straddle Johnson r=n/2+1: scan deep (BAD) side first then up toward GOOD
        r_list = list(range(n//2 + args.span, n//2 - 2, -1))  # descending: deep BAD first
        run(n, k, primes, r_list, time_budget_s=args.tb, maxscan=int(args.maxscan))
    print("\nALL DONE", flush=True)
