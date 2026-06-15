#!/usr/bin/env python3
"""WF407 / T334-13-M3 : the M3 signal-strength scaling law (task 2 crux).

Uses the cross-validated decomp engine (probe_agreement_m3_decomp.py) to measure the
SMOOTH-vs-RANDOM M3 separation at FIXED n as q grows, isolating the relative signal
    rel(q) = |M3_sub[2,2,2] - M3_rand[2,2,2]| / M3_sub[2,2,2].
RESULTS-M3 measured rel ~ 1.9e-11 (q=113) and 5.6e-13 (q=257) at n=16, and conjectured
rel ~ q^-4 at fixed n.  If rel ~ q^-c with c >= 1, then at prize q ~ 2^128 the signal is
<= 2^-128, i.e. at or below the e* = 2^-128 resolution -- the M3 separation is real but
CANNOT move a 2^-128-resolution tail.  This probe pins the exponent c.

For each q (q == 1 mod n, q prime) we run the engine on the order-n subgroup and on a few
random n-subsets; rel is the min over randoms at the (k-1,k-1,k-1) cell.  Exact integers.

Reproduce:  python wf407_T334-13-M3_signal_scaling.py
"""

import json
import math
import random
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ENGINE = HERE / "moments" / "probe_agreement_m3_decomp.py"


def is_prime(m):
    if m < 2:
        return False
    f = 2
    while f * f <= m:
        if m % f == 0:
            return False
        f += 1
    return True


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q):
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e)
        e = (e * h) % q
    return sorted(out)


def run_engine(q, k, domain, census=False):
    cmd = [sys.executable, str(ENGINE), "--q", str(q), "--k", str(k),
           "--domain", ",".join(map(str, domain))]
    if census:
        cmd.append("--census")
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"engine failed q={q}: {r.stderr[-500:]}")
    return json.loads(r.stdout)


def cell(q, n, k, cellkey, nrand=4):
    H = subgroup(q, n)
    sub = run_engine(q, k, H)
    msub = sub["M3"].get(cellkey, 0)
    best = None
    for seed in range(1, nrand + 1):
        dom = sorted(random.Random(7919 * q + seed).sample(range(1, q), n))
        rd = run_engine(q, k, dom)
        d = abs(msub - rd["M3"].get(cellkey, 0))
        if best is None or d < best:
            best = d
    rel = best / msub if msub else 0.0
    return msub, best, rel


def main():
    print("WF407 / T334-13-M3 : M3 signal-strength scaling rel(q) at fixed n")
    print("(decomp engine, exact integers; rel = |dM3|/M3 at (k-1,k-1,k-1))\n")
    n, k = 8, 3
    cellkey = f"{k-1},{k-1},{k-1}"  # (2,2,2)
    # primes q == 1 mod 8 (so mu_8 exists), increasing
    qs = [q for q in range(17, 2200) if is_prime(q) and (q - 1) % n == 0]
    qs = qs[:14]
    print(f"n={n}, k={k}, separating cell {cellkey}; primes q==1 mod {n}:")
    print(f"{'q':>6}{'M3[2,2,2]':>26}{'|dM3|':>22}{'rel=|dM3|/M3':>16}{'rel*q^4':>14}")
    data = []
    for q in qs:
        msub, dm, rel = cell(q, n, k, cellkey)
        data.append((q, rel))
        print(f"{q:>6}{msub:>26}{dm:>22}{rel:>16.4e}{rel*q**4:>14.4g}")
    # fit log rel = -c log q + b  (least squares on the larger q half)
    pts = [(math.log(q), math.log(rel)) for (q, rel) in data if rel > 0]
    if len(pts) >= 3:
        tail = pts[len(pts)//2:]
        xs = [x for x, _ in tail]; ys = [y for _, y in tail]
        mx = sum(xs)/len(xs); my = sum(ys)/len(ys)
        c = -sum((x-mx)*(y-my) for x,y in zip(xs,ys)) / sum((x-mx)**2 for x in xs)
        print(f"\nfitted exponent c in rel ~ q^-c  (tail half): c = {c:.3f}")
        # extrapolate to prize q ~ 2^128
        q_prize = 2.0**128
        rel_prize_loglog = math.exp(my) * (math.exp(mx)/q_prize)**(-(-c))
        # use the fit line: log rel = my + (-c)(log q - mx)
        log_rel_prize = my + (-c)*(math.log(q_prize) - mx)
        print(f"extrapolated rel at q=2^128: ~ 2^{log_rel_prize/math.log(2):.1f}")
        print(f"prize resolution e* = 2^-128.  M3 signal {'BELOW' if log_rel_prize/math.log(2) < -128 else 'ABOVE'} resolution.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
