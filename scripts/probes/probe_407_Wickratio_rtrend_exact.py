#!/usr/bin/env python3
"""
probe_407_Wickratio_rtrend_exact.py  (#444)

LANE (uncontested, CHAR-0, control-free, distinct from the live mod-p anomaly-predictor worker):
The prize-relevant object is the WICK RATIO W_r = E_r^(0)(mu_n)/((2r-1)!! n^r) -- which I showed
(push 58f29f3f0) EQUALS the accumulated moment-step product prod_{s<r} g(s). The Gaussian/random model
has W_r = 1; the thin subgroup has W_r < 1 (a deficit = thin advantage). The OPEN question (DISPROOF_LOG
residual): as the moment ORDER r grows toward prize depth r*~log n, does the thin Wick-deficit (1 - W_r)
GROW (compounding advantage that could survive the joint limit) or stay TIED to the leading R(R-1)/2n
(knife-edge)?

This is FULLY EXACT (char-0 cyclotomic-lattice convolution, NO stochastic control, NO prime) -- it fixes
the broken neg-random control of the prior attempt by comparing to the EXACT Wick target instead.

KEY QUANTITY: define D_r := (1 - W_r) * n  (the deficit rescaled by n). From log W_R = -R(R-1)/(2n)+..,
W_R ~ 1 - R(R-1)/(2n), so D_r ~ r(r-1)/2 to leading order. The QUESTION is whether the EXACT D_r tracks
r(r-1)/2 (pure leading, knife-edge -> W->1) or whether D_r/n^0 has an EXTRA piece growing FASTER in r
(e.g. ~ r^2 log, or an exponential-in-r factor) that, at r*~log n, would keep W_{r*} bounded below 1.
Compute D_r EXACTLY for r=2..8, n=8..64, and read the r-growth of D_r and of D_r vs r(r-1)/2.

NO LEAN. Exact integer cyclotomic-lattice convolution => axiom-clean trivially.
"""
import math
from collections import Counter

def Er0_thin(n, R):
    """Exact char-0 additive energies E_r^(0)(mu_n), r=1..R, via r-fold convolution in Z^{n/2}
    (mu_n = n-th roots of unity, n=2^a, zeta^{n/2}=-1 => each root is +/- a basis vector e_{i mod n/2})."""
    half = n // 2
    pts = [(i % half, 1 if i < half else -1) for i in range(n)]
    h = {tuple([0]*half): 1}
    out = {}
    for r in range(1, R + 1):
        nh = Counter()
        for v, c in h.items():
            for (j, s) in pts:
                w = list(v); w[j] += s; nh[tuple(w)] += c
        h = nh
        out[r] = sum(c * c for c in h.values())
    return out

def dfac(r):
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v

print("=" * 84)
print("EXACT char-0 Wick ratio W_r = E_r^(0)(mu_n)/((2r-1)!! n^r) and deficit (1-W_r), r-trend")
print("(W_r = accumulated moment-step product; Gaussian model W_r=1; thin deficit = thin advantage)")
print("=" * 84)
from fractions import Fraction
Rmax_by_n = {8: 8, 16: 7, 32: 6, 64: 4}  # cap r so the lattice convolution stays tractable
data = {}
for n in [8, 16, 32, 64]:
    R = Rmax_by_n[n]
    E = Er0_thin(n, R)
    data[n] = E
    print(f"--- n={n} (E_r exact up to r={R}) ---")
    for r in range(2, R + 1):
        W = Fraction(E[r], dfac(r) * n**r)
        Dr = (1 - W) * n               # rescaled deficit
        lead = Fraction(r*(r-1), 2)    # predicted leading D_r
        print(f"  r={r}: W_r={float(W):.6f}  (1-W_r)={float(1-W):.6f}  D_r=(1-W)*n={float(Dr):.4f}  "
              f"r(r-1)/2={float(lead):.1f}  D_r-lead={float(Dr-lead):+.4f}")
print()
print("=" * 84)
print("r-TREND of the EXACT deficit D_r=(1-W_r)*n vs the leading r(r-1)/2, at the largest feasible n")
print("=" * 84)
for n in [16, 32]:
    R = Rmax_by_n[n]
    E = data[n]
    print(f"--- n={n} ---")
    ratios = []
    for r in range(2, R + 1):
        W = Fraction(E[r], dfac(r) * n**r)
        Dr = float((1 - W) * n)
        lead = r*(r-1)/2
        ratios.append((r, Dr/lead))
    print("  D_r / [r(r-1)/2]  (=1 means pure leading=knife-edge; >1 and GROWING = extra thin advantage):")
    print("   " + "  ".join(f"r={r}:{v:.3f}" for r, v in ratios))
    vs = [v for _, v in ratios]
    if all(vs[i+1] > vs[i] for i in range(len(vs)-1)):
        print("   => RATIO GROWS with r: D_r exceeds the leading r(r-1)/2 by a WIDENING margin.")
        print("      The exact thin deficit is SUPER-leading => a compounding thin advantage beyond")
        print("      the -R(R-1)/2n knife-edge. At r*~log n this EXTRA piece could keep W_{r*} below 1.")
    elif all(vs[i+1] < vs[i] for i in range(len(vs)-1)):
        print("   => RATIO SHRINKS toward/below 1: D_r is at-or-below the leading r(r-1)/2 => the")
        print("      knife-edge dominates, no surviving extra thin advantage.")
    else:
        print("   => non-monotone -- read per-r.")
print()
print("HONEST: char-0 EXACT, no control, no prime. The verdict is the r-growth of D_r/[r(r-1)/2]:")
print("super-leading (grows) = a LIVE compounding thin advantage candidate; tied/sub (->1 or below) =")
print("the BGK knife-edge dominates. Either way maps the deep-r structure of the surviving thin lever.")
print("CORE not closed, not refuted.")
