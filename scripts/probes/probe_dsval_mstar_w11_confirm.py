#!/usr/bin/env python3
"""
RULE-6 confirmation: all-direction w=11 (m*=3) incidence at n=32, per-direction, to PIN w*=11.
Uses the validated rotation-reduced exact mod-p engine. Prints every direction whose I exceeds a
report threshold, and the global max. If global max <= budget=32, then w*=11 => m*=3 is RIGOROUSLY
the crossing (since w=10 worst was 3872 > 32 and incidence is monotone non-increasing in w).
"""
import sys, math, time
import numpy as np
sys.path.insert(0, "scripts/probes")
import probe_dsval_mstar_rotreduced as R

def main(n, k, w, beta=4.0, report_thresh=20):
    p, mu, m, h = R.build_field(n, beta)
    budget = n
    print(f"[w={w} confirm] n={n} k={k} p={p} m={m} PROPER mu_n budget={budget}", flush=True)
    INV = R.build_inv_table(p)
    Vall = np.array([[pow(mu[i], j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    dirs = [(a, b) for a in range(k, n) for b in range(a+1, n)]
    print(f"  {len(dirs)} directions, C(n-1,w-1)={math.comb(n-1,w-1)}", flush=True)
    gmax = 0; gdir = None; t0 = time.time(); over = []
    for ci, (a, b) in enumerate(dirs):
        xa = np.array([pow(mu[i], a, p) for i in range(n)], dtype=np.int64)
        xb = np.array([pow(mu[i], b, p) for i in range(n)], dtype=np.int64)
        _, seen = R.incidence_dir_rot(Vall, xa, xb, n, k, w, p, INV)
        I = R.orbit_closure_count(seen, h, (b-a) % n, n, p)
        if I > gmax: gmax = I; gdir = (a, b)
        if I > report_thresh:
            print(f"    dir({a},{b}) step={b-a} I={I}{' >BUDGET' if I>budget else ''}", flush=True)
        if I > budget:
            over.append(((a, b), I))
        if ci % 20 == 0:
            print(f"    ...{ci+1}/{len(dirs)} done, running max={gmax}@{gdir} ({time.time()-t0:.0f}s)", flush=True)
    print(f"  GLOBAL w={w} m*={w-k} worstI={gmax} dir={gdir} [{'>budget' if gmax>budget else '<=budget'}]", flush=True)
    print(f"  directions exceeding budget: {over}", flush=True)
    if gmax <= budget:
        print(f"  => w*={w} CONFIRMED (m*={w-k}, delta*=1-{w}/{n}={1-w/n:.5f}). BOUNDED m* at n={n}.", flush=True)
    else:
        print(f"  => some dir exceeds budget at w={w}; w*>{w}, recheck higher w.", flush=True)

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    w = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    main(n, k, w)
