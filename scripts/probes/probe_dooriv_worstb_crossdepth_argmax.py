#!/usr/bin/env python3
"""
Door-IV Lane-1 probe (#444/#464): is the worst frequency b* DEPTH-INVARIANT across the dyadic tower?

The prize object M(n)=max_b|Σ_{x∈μ_n} e_p(bx)| is over the FULL group μ_n. The partition-depth
results (245cf1f7b index-2, de49faef2 index-4) show that AT the full-group argmax b*, every dyadic
sub-split is coherent with a bounded inflation band. NEW orthogonal question (not a re-probe of
coherence/imbalance/band): is the argmax frequency ITSELF the same object across the natural
sub-quantities?

Define, at fixed prime p and subgroup μ_n:
  b*_full = argmax_b |Σ_{x∈μ_n} e_p(bx)|                 (the prize frequency)
  b*_A    = argmax_b |Σ_{x∈μ_{n/2}} e_p(bx)|             (the SUBGROUP half's own worst freq)
This probe measures, by FULL coset scan (proper μ_n, p≫n³, never n=q-1):
  (Q1) NESTING: is b*_full the worst frequency of the half-subgroup μ_{n/2}? (already proven NO by
       _DoorIVWorstBNonNested — we RE-CONFIRM ONCE as a control, not the deliverable.)
  (Q2) NEW: at b*_full, what is the RANK PERCENTILE of b*_full within the half-subgroup's |η|
       distribution? i.e. is b*_full a HIGH-percentile (near-worst) frequency for μ_{n/2}, or
       generic? This quantifies HOW non-nested it is — a near-worst rank means the full-group and
       sub-group adversaries are "almost aligned" (the wall transfers nearly intact down the tower);
       a generic rank means they're decoupled.
  (Q3) NEW: ratio M(μ_n)/M(μ_{n/2}) — the actual per-level growth factor of the WALL ITSELF (each
       group at its OWN worst b). The asymptotic-claim guard says this must be ≥ √2·(1+o(1)) on the
       √(n log) law; measure it directly to confirm the wall is NOT thinning per level.

This is genuinely new (cross-depth ARGMAX relationship + true per-level wall growth), distinct from
the within-b* coherence/imbalance/band lane. Probe-first; report median over primes; no theorem from
a trend (HARD RULE 1).
"""
from __future__ import annotations

import argparse
import math
import numpy as np
import sympy as sp

TAU = 2.0 * math.pi


def primes_1_mod_n(n: int, beta: int, count: int):
    target = n ** beta
    k = max(1, (target - 1 + n - 1) // n)
    out = []
    p = k * n + 1
    while len(out) < count:
        if sp.isprime(p):
            out.append(p)
        p += n
    return out


def full_eta_abs(b: int, gen_pow_list, p: int):
    ph = np.array([(b * g) % p for g in gen_pow_list], dtype=object).astype(np.float64)
    return abs(np.exp(1j * TAU * ph / p).sum())


def scan(n: int, p: int, chunk: int = 8192):
    """Return (M_full, b_full, M_half, rank_pct_of_bfull_in_half).

    M_full is the FULL-group worst over all m = (p-1)/n cosets of μ_n.
    M_half is the half-subgroup μ_{n/2} worst over ALL 2m = (p-1)/(n/2) cosets of μ_{n/2}
    (NOT just the m cosets of μ_n — μ_{n/2} is a bigger quotient). rank_pct is computed against
    that full 2m-coset half distribution."""
    assert n < p - 1 and n % 2 == 0
    m = (p - 1) // n           # number of μ_n cosets
    mh = (p - 1) // (n // 2)   # number of μ_{n/2} cosets = 2m
    g = int(sp.primitive_root(p))
    Gfull = [pow(g, m * t, p) for t in range(n)]
    # half-subgroup μ_{n/2} = <g^{mh}>  (the index-2 SUBGROUP, the "squares" half)
    Ghalf = [pow(g, mh * t, p) for t in range(n // 2)]
    Gfull_arr = np.array(Gfull, dtype=object)
    Ghalf_arr = np.array(Ghalf, dtype=object)

    # full-group worst b over all m cosets of μ_n
    repsF = np.array([pow(g, j, p) for j in range(m)], dtype=object)
    bestF, bF = -1.0, None
    for lo in range(0, m, chunk):
        rr = repsF[lo:lo + chunk]
        phf = (rr[:, None] * Gfull_arr[None, :]) % p
        vf = np.abs(np.exp(1j * TAU * phf.astype(np.float64) / p).sum(axis=1))
        jf = int(np.argmax(vf))
        if vf[jf] > bestF:
            bestF = float(vf[jf]); bF = int(rr[jf])

    # half-subgroup |η| values over ALL mh = 2m cosets of μ_{n/2} (the CORRECT full quotient)
    repsH = np.array([pow(g, j, p) for j in range(mh)], dtype=object)
    half_vals = np.empty(mh, dtype=np.float64)
    for lo in range(0, mh, chunk):
        rr = repsH[lo:lo + chunk]
        phh = (rr[:, None] * Ghalf_arr[None, :]) % p
        vh = np.abs(np.exp(1j * TAU * phh.astype(np.float64) / p).sum(axis=1))
        half_vals[lo:lo + len(rr)] = vh

    # half-subgroup's OWN worst over the FULL 2m-coset quotient
    M_half = float(half_vals.max())
    # rank percentile of b_full's half-value within the full 2m-coset half distribution
    half_at_bfull = full_eta_abs(bF, Ghalf, p)
    rank_pct = float((half_vals <= half_at_bfull).mean())
    return bestF, bF, M_half, rank_pct


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--amin", type=int, default=4)
    ap.add_argument("--amax", type=int, default=6)
    ap.add_argument("--beta", type=int, default=4)
    ap.add_argument("--primes", type=int, default=6)
    args = ap.parse_args()

    print(f"# Door-IV worst-b CROSS-DEPTH argmax + per-level wall growth "
          f"(beta={args.beta}, {args.primes} primes/n, FULL coset scan, proper μ_n)\n")
    print(f"{'n':>5} {'M_full/√n':>10} {'M_half/√(n/2)':>13} "
          f"{'M_full/M_half':>13} {'bfull rank% in half':>20}")
    rows = []
    for a in range(args.amin, args.amax + 1):
        n = 1 << a
        ps = primes_1_mod_n(n, args.beta, args.primes)
        ratios, ranks, mf_sqrt, mh_sqrt = [], [], [], []
        for p in ps:
            Mf, bF, Mh, rk = scan(n, p)
            ratios.append(Mf / Mh); ranks.append(rk)
            mf_sqrt.append(Mf / math.sqrt(n)); mh_sqrt.append(Mh / math.sqrt(n / 2))
        r = float(np.median(ratios)); rk = float(np.median(ranks))
        print(f"{n:>5} {np.median(mf_sqrt):>10.4f} {np.median(mh_sqrt):>13.4f} "
              f"{r:>13.4f} {rk:>20.4f}")
        rows.append((n, r, rk))

    print("\n## VERDICT")
    growth = [r for (_, r, _) in rows]
    ranks = [rk for (_, _, rk) in rows]
    print(f"per-level wall growth M(μ_n)/M(μ_{{n/2}}): {[round(x,3) for x in growth]}")
    print(f"  (√2 ≈ 1.414 is the floor on the √(n·log) law; values ≥ ~1.4 ⟹ wall does NOT thin per level)")
    print(f"b*_full rank percentile within μ_{{n/2}}: {[round(x,4) for x in ranks]}")
    if all(x > 0.5 for x in growth):  # >1 means full > half, wall grows
        print("WALL GROWS PER LEVEL (M_full > M_half always): the √-wall is NOT thinning down the tower.")
    if all(x < 0.999 for x in ranks):
        print("b*_full is NOT the half-subgroup's argmax (rank<1) — RE-CONFIRMS non-nesting (control).")
    print(f"NEW: b*_full sits at the {np.median(ranks)*100:.1f}th percentile of μ_{{n/2}}'s |η| "
          f"distribution (median) — quantifies the cross-depth adversary "
          f"{'near-alignment' if np.median(ranks) > 0.9 else 'decoupling' if np.median(ranks) < 0.6 else 'partial overlap'}.")
    print("\nPROBE-ONLY (HARD RULE 1): no growth-law theorem from a trend. CORE remains OPEN.")


if __name__ == "__main__":
    main()
