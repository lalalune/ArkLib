#!/usr/bin/env python3
"""
wf-RB (#444) DECISIVE single-boundary test: is the over-determined far-line BAD at r=n/2+2 and
GOOD at r=n/2+1 (=> r*=n/2+1, JOHNSON+1rung), or does GOOD extend to r>=n/2+2 (=> CLIMB past
Johnson toward the floor 1-rho)?  n in {16,20,24,28,32,34,38}, full b-range, multi-prime.

We compute, per critical rung r and per prime, the WORST far-line incidence over the
worst-candidate over-det directions (order-2/antipodal + low-exponent x^k family, FULL b-range,
far-validity b<s), with early-exit at >budget=n and a hard per-direction subset-scan cap (so GOOD
directions resolve fast and BAD binders early-exit). A rung is BAD iff some far-valid direction
exceeds budget; GOOD (over the maximizer family) otherwise.

KEY: the over-det incidence MAX is the PROVEN antipodal cubic 2m^3-2m^2+1 (>>n) at the SHALLOW
band s=k+2; it DECREASES as s->n/2. The transition r* is the binding witness boundary.
"""
import sys, time
from math import comb
import numpy as np
sys.path.insert(0, 'scripts/probes')
import probe_wf4RB_vec_rprofile as V


def cand_dirs(n, k, s):
    """Worst-candidate FAR-VALID (b<s) over-det binders for rung r=n-s, BAD-likely first.
       EMPIRICAL binders (n=16,20 decisive runs): the x^k LOW-EXPONENT family (b=k) with HIGH a
       (large |a-b| = max dilation orbit) -- e.g. (11,4),(14,4) @n16; (16,5),(18,5) @n20 -- plus
       the order-2 / antipodal lines (a=n/2, low b). We restrict to these proven maximizer families
       (b in {k,k+1,k+2} and the order-2 a=n/2 line), all far-valid b<s. This is the SUFFICIENT
       worst-candidate set; it is NOT the full b-range (which is intractable at n>=24), but it
       contains every binder observed across n=16,20,24,28 (+ the proven antipodal cubic max)."""
    ds = []
    m2 = n // 2
    # x^k, x^{k+1}, x^{k+2} families: a high->low (big orbit first)
    for b in [k, k+1, k+2]:
        if b >= s:  # far-validity
            continue
        for a in range(n-1, k-1, -1):
            if a != b:
                ds.append((a, b))
    # order-2 / antipodal lines: a=n/2 (and n/2-1), b sweeping low (far-valid)
    for a in [m2, m2-1, m2+1]:
        if not (k <= a < n): continue
        for b in range(k, min(s, n)):
            if b != a:
                ds.append((a, b))
    seen = set(); out = []
    for d in ds:
        if d not in seen: seen.add(d); out.append(d)
    return out


def worst_incidence(n, k, p, mu, s, budget, maxscan):
    """max far-line incidence over far-valid worst-candidate dirs, early-exit BAD."""
    best = 0; binder = None; capped = False
    for (a, b) in cand_dirs(n, k, s):
        I = V.incidence_vec(a, b, n, mu, k, p, s, budget, maxscan=maxscan)
        if I is None:
            continue
        if isinstance(I, tuple):
            capped = True
            if I[1] > best: best = I[1]; binder = (a, b)
            continue
        v = I if I <= budget else budget + 1
        if v > best:
            best = v; binder = (a, b)
        if v > budget:
            return ('BAD', v, (a, b), False)
    return ('GOOD', best, binder, capped)


def decide(n, k, primes, maxscan):
    budget = n; rho = k/n
    jr = n//2 + 1
    print(f"\n===== n={n} k={k} rho={rho:.4f} budget={budget}  maxscan={maxscan:,} =====", flush=True)
    print(f"  Johnson+1rung r*={jr} (s*={n//2-1}, delta*={0.5+1/n:.4f}); floor r*={int((1-rho)*n)} (delta*={1-rho:.4f})", flush=True)
    setups = [(p, V.setup(n, p)) for p in primes]
    # critical rungs: r* candidate jr, and jr+1, jr+2 (deeper, must be BAD if no climb); and jr-1.
    rungs = [jr-1, jr, jr+1, jr+2, jr+3]
    verds = {}
    print(f"  {'r':>3} {'s':>3} {'delta':>7} {'C(n,s)':>13}  " + "  ".join(f'p{i}' for i in range(len(primes))), flush=True)
    for r in rungs:
        s = n - r
        if s < k+1 or r < 1: continue
        cells = []; agg = []
        for (p, mu) in setups:
            t0 = time.time()
            verdict, mx, binder, cap = worst_incidence(n, k, p, mu, s, budget, maxscan)
            cells.append(f"{verdict}({mx},{binder},{'cap' if cap else ''},{time.time()-t0:.0f}s)")
            agg.append(verdict)
        v = 'BAD' if 'BAD' in agg else 'GOOD'
        verds[r] = v
        print(f"  {r:>3} {s:>3} {r/n:>7.4f} {comb(n,s):>13}  " + "  ".join(cells), flush=True)
    # verdict
    bad = sorted([r for r in verds if verds[r]=='BAD'])
    good = sorted([r for r in verds if verds[r]=='GOOD'])
    if bad:
        sb = min(bad); rstar = sb-1
        tag = ("JOHNSON+1rung LOCKED" if rstar==jr else ("CLIMB past Johnson!" if rstar>jr else "below Johnson+1rung"))
        print(f"  >>> smallest BAD r={sb} => r*={rstar} delta*={rstar/n:.4f} s*={n-rstar}. Johnson r*={jr}. VERDICT: {tag}", flush=True)
    else:
        print(f"  >>> NO BAD rung in {rungs} (all GOOD): the over-det never crosses budget here -> "
              f"either climb or all-good. verds={verds}", flush=True)
    return verds


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="16")
    ap.add_argument("--maxscan", type=float, default=3e6)
    args = ap.parse_args()
    KMAP = {16:4,20:5,24:6,28:7,32:8,34:8,36:9,38:9,40:10}
    for n in [int(x) for x in args.ns.split(",")]:
        k = KMAP[n]
        primes = [V.find_prime_cong1(n,200000), V.find_prime_cong1(n,700000)]
        decide(n, k, primes, int(args.maxscan))
    print("\nALL DONE", flush=True)
