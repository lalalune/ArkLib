#!/usr/bin/env python3
"""
A3 (#444) — clearing/saturation prime p*(n) at n=64 (feasible single-pencil cut).

The prior-art probe_nearcap_saturation_scaling measures p*(sat)/n^3 at n=16,32 cheaply but
n=64 (C(64,5)=7.62M subsets/prime) is too slow for the full 2-pencil x 8-prime sweep. This
probe takes the SINGLE most-near-capacity far pencil and the SINGLE closest-to-capacity band
and brackets its saturation threshold with a minimal prime ladder, to read the n=64 point of
the p*(sat) growth law. Combined with n=16,32 it answers: does p*(n) outrun the prize prime?

Near-capacity band = smallest w above k (w=k+1 is floppy/r=1; w=k+2 is the slowest-clearing
over-det band = the genuine wall). We track w=k+1 (floppy, must grow ~p) and w=k+2 (over-det,
must saturate) to LOCATE the n=64 saturation threshold of the slow over-det band.
"""
import sys, math, time
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from probe_charinv_constrate_n64 import isp, bandcounts  # noqa

def main():
    n, k = 64, 4                 # rho = 1/16
    n3 = n**3                    # 262144
    pencil = (5, 7)              # near-capacity-active far pencil (gcd 2), as in prior probe
    # prime ladder bracketing n^3 (262144): a few below, several above, up to ~50 n^3.
    cand = [193, 449, 65537, 262657, 786433, 1179649, 5767169, 13631489]
    primes = sorted(p for p in cand if isp(p) and (p-1) % n == 0)
    print(f"A3 n={n} k={k} rho={k/n} pencil={pencil} n^3={n3} capacity delta=1-rho={1-k/n}", flush=True)
    print(f"primes (1 mod {n}): {primes}", flush=True)
    a, b = pencil
    series = {}
    for p in primes:
        t0 = time.time()
        bc = bandcounts(p, n, k, a, b, verbose=False)
        series[p] = bc
        floppy = bc[k+1]; overdet = bc[k+2]; overdet2 = bc[k+3]
        print(f"  p={p:>9} (p/n^3={p/n3:6.2f}): floppy(w={k+1},d={1-(k+1)/n:.3f})I={floppy:>8} (I/p={floppy/p:.2e}) | "
              f"overdet(w={k+2},d={1-(k+2)/n:.3f})I={overdet:>6} | (w={k+3})I={overdet2:>5}  [{time.time()-t0:.0f}s]", flush=True)
    # saturation threshold of the over-det band w=k+2 (>n^3 only)
    big = [(p, series[p][k+2]) for p in primes if p > n3]
    if big:
        imax = max(v for _, v in big)
        thr = next((p for p, v in big if v >= 0.95*imax), None) if imax > 0 else None
        print(f"\n  over-det band w={k+2}: I_sat≈{imax}  p*(sat,>=95%)={thr}  "
              f"p*/n^3={None if thr is None else round(thr/n3,2)}", flush=True)
    # floppy growth check: does I(w=k+1)/p stay bounded away from 0 (genuine wall) ?
    fr = [(p, series[p][k+1]/p) for p in primes if p > n3]
    print(f"  floppy w={k+1} I/p over p>n^3: {[(p, round(f,4)) for p,f in fr]}", flush=True)
    print(f"  => floppy lower edge delta=1-(k+1)/n={1-(k+1)/n:.4f}; candidate (1-rho)-log2(n)/n="
          f"{(1-k/n)-math.log2(n)/n:.4f}; floppy-cand={(1-(k+1)/n)-((1-k/n)-math.log2(n)/n):+.4f}", flush=True)

if __name__ == "__main__":
    main()
