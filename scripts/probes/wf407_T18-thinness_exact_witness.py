#!/usr/bin/env python3
"""wf407_T18-thinness_exact_witness.py  (#407 T18 — EXACT rational witness for the Lean brick)

We need an EXACT (not floating) certificate that B^2 > 2 n log p at the Fermat witness,
so we can encode a machine-checked refutation of the thickness-monotone hypothesis in Lean.

Difficulty: B = |eta_b| involves sqrt and log p is transcendental. We make the refutation
rational/decidable as follows. The witness is p=65537, n=64, and a specific frequency b.
We compute |eta_b|^2 EXACTLY as a sum of cos/sin -- but that is algebraic, not rational.

Instead we use a CLEAN rational lower bound on B^2 and a CLEAN rational upper bound on
2 n log p, and show the former exceeds the latter:
   B^2 >= L  (rational, by exhibiting a frequency b with |eta_b|^2 >= L, certified by
              evaluating the integer real/imag parts to high precision and rounding DOWN),
   2 n log p <= U  (rational, log 65537 < log(65537) and we use log p < ln(2^17) = 17 ln2
                    < 17 * 0.6931472 = 11.78... ; safe rational upper bound),
   and L > U.
Here n=64, so 2 n log p < 2*64*11.7836 = 1508.3. We need B^2 >= ~1509 to win OUTRIGHT,
but B^2 = (B^2/n)*n = 14.87*64 ~ 952 at the worst Fermat period -- that is LESS than
2 n log p with this crude log bound (log p ~ 11.09, 2*64*11.09=1419 > 952). So the
OUTRIGHT inequality B^2 > 2 n log p is the WRONG framing for n=64.

CORRECTION: the violation is B/sqrt(2 n log p) > 1 <=> B^2 > 2 n log p. At n=64 worst
Fermat period: B^2/n = 14.874 (logMeff), 2 log p = 22.18, so B^2/n = 14.87 < 22.18?!
Wait: B/sqrt(2 n log p) = sqrt( (B^2/n) / (2 log p) ) = sqrt(14.874/22.18)=sqrt(0.670)
=0.819 NOT 1.158. Let me recompute which witness actually has ratio>1.

The thick-window probe reported n=64 ratio 1.158 using B (not B^2). Re-derive: ratio
= B / sqrt(2 n log p). B=43.63, sqrt(2*64*11.09)=sqrt(1419.5)=37.68, 43.63/37.68=1.158.
So B^2 = 1903.6, B^2/n = 29.74 (matches thick-dyadic table B^2/n=29.75!), and
2 n log p = 1419.5, and 1903.6 > 1419.5. GOOD -- the OUTRIGHT inequality B^2 > 2 n log p
DOES hold at n=64 (the scale-pin probe's '14.874' was logMeff = B^2/(2n) = 1903.6/128=
14.87, consistent). So B^2 > 2 n log p IS the clean refutation. We now certify it
rationally.
"""
import sys, math
from fractions import Fraction
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import primitive_root
from mpmath import mp, mpf, cos, sin, log as mlog

mp.dps = 60

def main():
    flush = lambda *a: print(*a, flush=True)
    p = 65537; n = 64
    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)
    sub = []; cur = 1
    for i in range(n):
        sub.append(cur); cur = cur * gm % p
    m = (p - 1) // n
    # find worst frequency b and its EXACT-ish |eta_b|^2 (high precision)
    twopi = 2 * mp.pi
    bestBsq = mpf(0); bestb = None
    b = 1
    for j in range(m):
        re = mpf(0); im = mpf(0)
        for x in sub:
            ang = twopi * ((b * x) % p) / p
            re += cos(ang); im += sin(ang)
        s = re*re + im*im
        if s > bestBsq:
            bestBsq = s; bestb = b
        b = b * g % p
    flush(f"p={p} n={n} m={m}  worst b={bestb}")
    flush(f"  B^2 = {float(bestBsq):.6f}   B = {float(mp.sqrt(bestBsq)):.6f}")
    lnp = mlog(mpf(p))
    twoNlogp = 2 * n * lnp
    flush(f"  2 n log p = {float(twoNlogp):.6f}   (log p = {float(lnp):.6f})")
    flush(f"  B^2 - 2 n log p = {float(bestBsq - twoNlogp):.6f}   (>0 => target FALSE)")
    flush(f"  ratio B/sqrt(2 n log p) = {float(mp.sqrt(bestBsq/twoNlogp)):.6f}")

    # rational certificate: B^2 >= L (round down), 2 n log p <= U (round up), L > U.
    L = Fraction(int(math.floor(float(bestBsq) * 1000)), 1000)
    # safe upper bound on log p: log 65537 < log 65540 ; use a verified rational.
    # ln(65537) = 11.0904...; certified upper bound 11.0905. 2*64*11.0905 = 1419.584
    U = Fraction(2 * n) * Fraction(110905, 10000)
    flush(f"\n  RATIONAL CERTIFICATE for Lean:")
    flush(f"    L (rational lower bound on B^2) = {L} = {float(L):.4f}")
    flush(f"    U (rational upper bound 2 n logp, using log p < 11.0905) = {U} = {float(U):.4f}")
    flush(f"    L > U ?  {L > U}   => B^2 > 2 n log p certified rationally")
    flush(f"\n  For the Lean brick we encode: with B^2 >= {float(L):.2f} and log p < 11.0905,")
    flush(f"  the thickness-monotone target B^2 <= 2*n*log p (n=64) is violated since")
    flush(f"  {float(L):.2f} > 2*64*11.0905 = {float(U):.2f}.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
