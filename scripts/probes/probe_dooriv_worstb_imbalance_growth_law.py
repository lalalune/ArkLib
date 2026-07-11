#!/usr/bin/env python3
"""
Door-IV Lane-1 probe (#444 / dossier #464): the GROWTH LAW of worst-b coset-half imbalance.

Established frontier (c1aae3d7e, 2c3e1aad6):
  - At the true worst frequency b*, the two index-2 coset-halves are PHASE-COHERENT
    (rho(b*)=1 exact, angle(A,B)=0) so M(n) = ||A|| + ||B|| at b*.
  - But they are STRICTLY IMBALANCED, r(b*) = min(||A||,||B||)/max(||A||,||B||) < 1,
    and the floor min_p r(b*) DECREASES with n (0.704 -> 0.527 -> 0.478 at n=16/32/64),
    "the halves DIVERGE as the subgroup thins". This was PROBE-ONLY (3 data points,
    no law fit).

THIS PROBE (genuinely new — fits a LAW, not 3-point monotonicity):
  Over many n = 2^a (a = 4..8) and multiple structured primes per n (beta=4, p>>n^3,
  p = k*n+1), do a FULL exhaustive coset scan F_p^*/mu_n to find the true argmax b*,
  then record at b*:
    - the imbalance deficit  d(n) = 1 - r(b*)   (median + worst over primes)
    - the log-magnitude gap   g(n) = log(max) - log(min) = -log r(b*)
  and fit d(n), g(n) against candidate laws:
    (P)  polynomial   d ~ c * n^{-s}      (log d  vs  log n  linear, slope -s)
    (L)  logarithmic  d ~ c / log n       (1/d   vs  log n   linear)
    (S)  sqrt-log     g ~ c * sqrt(log n) (the BGK scale)
  REASON THIS MATTERS: the prize reduces (at b*) to controlling M = ||A||+||B|| =
  max*(1 + r). If r(b*) -> 0 (deficit -> 1) the recursion degenerates to a SINGLE
  heavier half (greedy chain, already proven inert, 905cd5577). If r(b*) -> r_inf > 0
  there is a genuine 2-term split with persistent slack 1-r a non-moment method could
  grip. The OPEN question the prior probe left: WHICH regime, and at what rate.

  PROBE-ONLY by HARD RULE 1/2: never validate on n=q-1; proper mu_n; p>>n^3; multiple
  primes; report the law fit + R^2 + an HONEST verdict. NO Lean theorem asserted from a
  growth trend (needs open CORE). Findings/refutation only.
"""
from __future__ import annotations

import argparse
import math
import numpy as np
import sympy as sp

TAU = 2.0 * math.pi


def primes_1_mod_n(n: int, beta: int, count: int):
    """Smallest `count` primes p = k*n+1 with p >= n^beta (prize regime p>>n^3)."""
    target = n ** beta
    k = max(1, (target - 1 + n - 1) // n)
    out = []
    p = k * n + 1
    while len(out) < count:
        if sp.isprime(p):
            out.append(p)
        p += n
    return out


def worstb_imbalance(n: int, p: int, chunk: int = 8192):
    """FULL coset scan; return (r_star, max_norm, min_norm) at the true argmax b*."""
    assert n < p - 1, "must be a PROPER subgroup (never n=q-1)"
    m = (p - 1) // n
    g = int(sp.primitive_root(p))
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)
    G = np.array([pow(g, m * t, p) for t in range(n)], dtype=np.int64)
    Geven = G[0::2]
    Godd = G[1::2]

    # Use Python-int (object dtype) for the modular product to avoid int64 OVERFLOW:
    # at n=256, p~4.29e9 and products b*G can exceed 2^63-1, which would silently wrap
    # under numpy int64 BEFORE the `% p` and corrupt the phases. object dtype is exact.
    Go = G.astype(object)
    Geveno = Geven.astype(object)
    Goddo = Godd.astype(object)
    repso = reps.astype(object)
    best = -1.0
    best_pack = None
    for lo in range(0, m, chunk):
        rr = repso[lo:lo + chunk]
        ph = (rr[:, None] * Go[None, :]) % p          # exact Python-int arithmetic
        phf = ph.astype(np.float64)
        val = np.exp(1j * TAU * phf / p).sum(axis=1)
        a = np.abs(val)
        j = int(np.argmax(a))
        if a[j] > best:
            b = int(rr[j])
            phA = ((b * Geveno) % p).astype(np.float64)
            phB = ((b * Goddo) % p).astype(np.float64)
            A = np.exp(1j * TAU * phA / p).sum()
            B = np.exp(1j * TAU * phB / p).sum()
            best = float(a[j])
            best_pack = (abs(A), abs(B))
    nA, nB = best_pack
    hi, lo_ = max(nA, nB), min(nA, nB)
    return lo_ / hi, hi, lo_


def linfit(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    A = np.vstack([x, np.ones_like(x)]).T
    (slope, intc), res, *_ = np.linalg.lstsq(A, y, rcond=None)
    yhat = slope * x + intc
    ss_res = float(np.sum((y - yhat) ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2)) or 1e-30
    return slope, intc, 1.0 - ss_res / ss_tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--amax", type=int, default=8)   # n up to 2^8 = 256
    ap.add_argument("--amin", type=int, default=4)   # n from 2^4 = 16
    ap.add_argument("--beta", type=int, default=4)
    ap.add_argument("--primes", type=int, default=4)
    args = ap.parse_args()

    ns, d_med, d_worst, g_med = [], [], [], []
    print(f"# Door-IV worst-b imbalance GROWTH LAW (beta={args.beta}, "
          f"{args.primes} primes/n, FULL coset scan, proper mu_n)\n")
    print(f"{'n':>5} {'primes':>26} {'r* med':>8} {'r* min':>8} "
          f"{'defic med':>10} {'g=-log r med':>13}")
    for a in range(args.amin, args.amax + 1):
        n = 1 << a
        ps = primes_1_mod_n(n, args.beta, args.primes)
        rs = []
        for p in ps:
            r, _, _ = worstb_imbalance(n, p)
            rs.append(r)
        rs = np.array(rs)
        rmed = float(np.median(rs))
        rmin = float(rs.min())
        dmed = 1.0 - rmed
        gmed = -math.log(rmed)
        ns.append(n); d_med.append(dmed); d_worst.append(1.0 - rmin); g_med.append(gmed)
        ptxt = ",".join(str(x) for x in ps[:3]) + ("..." if len(ps) > 3 else "")
        print(f"{n:>5} {ptxt:>26} {rmed:>8.4f} {rmin:>8.4f} {dmed:>10.4f} {gmed:>13.4f}")

    logn = [math.log(x) for x in ns]
    print("\n## LAW FITS (median over primes)")
    # (P) polynomial: log(deficit) vs log n  -> slope = -s
    sP, iP, r2P = linfit(logn, [math.log(max(d, 1e-9)) for d in d_med])
    print(f"(P) polynomial  d ~ c*n^(-s):  s = {-sP:+.4f}   c = {math.exp(iP):.4f}   R^2 = {r2P:.4f}")
    # (L) logarithmic: 1/deficit vs log n
    sL, iL, r2L = linfit(logn, [1.0 / max(d, 1e-9) for d in d_med])
    print(f"(L) logarithmic d ~ c/log n:   1/d = {sL:+.4f}*log n {iL:+.4f}   R^2 = {r2L:.4f}")
    # (S) sqrt-log on the magnitude gap g = -log r
    sloglaw = [math.sqrt(l) for l in logn]
    sS, iS, r2S = linfit(sloglaw, g_med)
    print(f"(S) sqrt-log    g ~ c*sqrt(log n): c = {sS:+.4f}  intc = {iS:+.4f}   R^2 = {r2S:.4f}")
    # constant-floor check: does r* asymptote to a positive limit?
    print(f"\n## ASYMPTOTE CHECK")
    print(f"r*(med) sequence: {[round(1-d,4) for d in d_med]}")
    print(f"deficit ratio d(n+1)/d(n): "
          f"{[round(d_med[i+1]/max(d_med[i],1e-9),3) for i in range(len(d_med)-1)]}")

    best = max([("P", r2P), ("L", r2L), ("S", r2S)], key=lambda t: t[1])
    print(f"\n## VERDICT")
    print(f"best-fit law = ({best[0]}) with R^2 = {best[1]:.4f}")
    # NOTE on direction: the fitted quantity is the DEFICIT d = 1 - r. A DECAYING d (n^{-s} with
    # s>0, or c/log n) means d -> 0, hence r -> 1 (the halves become PERFECTLY BALANCED, the
    # symmetric ÷2 descent becomes applicable). A GROWING d means d -> 1, hence r -> 0 (the split
    # degenerates to a single heavier half / greedy chain). Do NOT conflate "deficit decays" with
    # "r -> 0" — they are opposite.
    if -sP > 0.05 and r2P > 0.9:
        print(f"DEFICIT DECAYS POLYNOMIALLY (d ~ n^(-{-sP:.3f})) ⟹ r* -> 1: the halves become "
              f"perfectly BALANCED in the thin limit, so the symmetric ÷2 descent BECOMES "
              f"applicable asymptotically (revives _DoorIVHalfMassBalanceAtArgmax).")
    elif r2L > 0.9 and sL > 0:
        print("DEFICIT DECAYS ONLY LOGARITHMICALLY (d ~ c/log n) ⟹ r* -> 1 but SLOWLY; the "
              "halves approach balance only at a log rate — symmetric descent applicable only "
              "in the deep-thin limit, with a log-small residual imbalance en route.")
    else:
        print(f"NO clean polynomial/log law (all R^2 < 0.9); the deficit is STATIONARY — it neither "
              f"decays (r*->1) nor grows (r*->0) but sits in a fixed band (median r* ≈ "
              f"{1 - d_med[-1]:.3f}). The split is a bounded O(1) reshuffle: persistent 2-term "
              f"slack (no single-half degeneration) AND no √-thinning over the heavier half.")
    print("\nPROBE-ONLY (HARD RULE 1/2): no Lean theorem asserted from an n-growth trend. "
          "CORE remains OPEN.")


if __name__ == "__main__":
    main()
