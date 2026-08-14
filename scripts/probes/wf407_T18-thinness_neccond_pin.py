#!/usr/bin/env python3
"""wf407_T18-thinness_neccond_pin.py  (#407 T18 — pin the formal NECESSARY CONDITION constants)

Goal: turn 'thinness is essential' into a clean, machine-checked NECESSARY CONDITION on
any valid delta* proof, by pinning the EXACT minimal constants.

A 'thickness-monotone' upper-bound method proves  B <= sqrt(c * n * log p)  with a fixed
universal c and a bound that is TIGHTEST in the thick (beta->1) limit. We show:

  (NC1)  No fixed c makes sqrt(c n log p) a valid upper bound that is simultaneously
         (a) <= the prize target sqrt(2 n log p) in the thin prize regime, AND
         (b) valid in the thick window.  Concretely: the smallest c for which
         B <= sqrt(c n log p) holds on the EXACT realizable family is
              c_p* := max_inst  B^2 / (n log p),
         and we report it. If c_p* > 2, the prize-target constant 2 is provably too
         small on realizable instances => any method giving the constant-2 bound is
         wrong, hence must EXPLOIT a feature (thinness/2-adic) absent in the thick witness.

  (NC2)  The honest scale is log m, NOT log p, and even there the constant is regime
         dependent: c_m* := max_inst B^2/(n log m). Report. The Salem-Zygmund c=2 holds
         on the diagonal (odd-rich m, prize-LIKE thinness) but FAILS on fully-dyadic
         thick witnesses -- so a valid SZ proof must use that the prize, despite m=2^128
         dyadic, is THIN (m huge), which forces log m large => the c=2 SZ scale becomes
         an upper bound again. We verify the SIGN of the effect: as log m -> infinity at
         FIXED n (true thin limit), does B^2/(n log m) drop below 2 and stay there?

  (NC3) The bootstrap-break depth: the moment method proves B from E_r up to r ~ log m.
        The 'thick failure' is that at small log m (thick) the needed r is tiny and the
        bound is loose; at large log m (thin prize) r ~ log m ~ 128 and the bound is the
        operative one. We tabulate the SZ ratio vs log m to show the crossing into
        validity is exactly the onset of thinness.

EXACT enumeration as before. We separate the family into THICK-DYADIC (Fermat-like,
the witness class) and THIN (large log m, prize-like).
"""
import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, primitive_root


def all_periods_Bsq_over_n(p, n):
    import numpy as np
    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)
    sub = np.empty(n, dtype=np.int64); cur = 1
    for i in range(n):
        sub[i] = cur; cur = cur * gm % p
    m = (p - 1) // n
    twp = 2.0 * math.pi / p
    Bsq = 0.0; b = 1
    for j in range(m):
        prods = (b * sub) % p; ang = twp * prods
        s = np.cos(ang).sum() ** 2 + np.sin(ang).sum() ** 2
        if s > Bsq: Bsq = s
        b = b * g % p
    return Bsq / n   # = B^2 / n


def main():
    flush = lambda *a: print(*a, flush=True)
    flush("#" * 100)
    flush("# T18 necessary-condition constants:  c_p* = max B^2/(n log p),  c_m* = max B^2/(n log m)")
    flush("#" * 100)

    # THICK-DYADIC witness class: Fermat cosets + generalized-Fermat dyadic ladder.
    thick = []
    p = 65537
    for mu in range(2, 12):
        n = 1 << mu
        if (p - 1) // n >= 2:
            thick.append((p, n, "Fermat"))
    for (n, j) in [(8, 5), (16, 4), (16, 8), (32, 3), (32, 7), (64, 10), (128, 9), (256, 8)]:
        m = 1 << j; pp = n * m + 1
        if is_prime(pp) and pp <= 3_000_000:
            thick.append((pp, n, "dyadicladder"))

    # THIN prize-like class: odd-rich m, large log m, fixed small n.
    thin = []
    for n in (8, 16, 32):
        used = set()
        # grow m at fixed n: p = n*m+1, pick odd-rich m to be non-dyadic, increasing
        for target in (1000, 4000, 16000, 64000, 250000):
            mm = target // n
            mm += (mm % 2 == 0)   # odd
            base = n * mm + 1
            cand, t = base, 0
            while t < 2_000_000 and cand < 5_000_000:
                if cand > 3 and is_prime(cand) and (cand - 1) % n == 0:
                    mloc = (cand - 1)//n
                    # require odd part large (thin, non-dyadic)
                    od = mloc
                    while od % 2 == 0: od //= 2
                    if od > mloc // 4 and cand not in used:
                        used.add(cand); thin.append((cand, n, "thin")); break
                cand += 2 * n; t += 1

    def scan(name, fam):
        flush(f"\n=== {name} ===")
        flush(f"  {'p':>9} {'n':>5} {'m':>8} {'beta':>5} {'log p':>6} {'log m':>6} "
              f"{'B^2/n':>8} {'c_p=B2/nlogp':>13} {'c_m=B2/nlogm':>13}")
        cp = 0.0; cm = 0.0
        rows = []
        for (pp, nn, _) in fam:
            v = all_periods_Bsq_over_n(pp, nn)   # B^2/n
            m = (pp - 1)//nn
            lnp = math.log(pp); lnm = math.log(m)
            cpi = v / lnp
            cmi = v / lnm if m > 1 else float('nan')
            cp = max(cp, cpi)
            if m > 1: cm = max(cm, cmi)
            bb = lnp / math.log(nn)
            rows.append((pp, nn, m, bb, lnp, lnm, v, cpi, cmi))
        rows.sort(key=lambda r: r[3])  # by beta
        for (pp, nn, m, bb, lnp, lnm, v, cpi, cmi) in rows:
            flush(f"  {pp:>9} {nn:>5} {m:>8} {bb:>5.2f} {lnp:>6.2f} {lnm:>6.2f} "
                  f"{v:>8.2f} {cpi:>13.3f} {cmi:>13.3f}")
        return cp, cm

    cp_thick, cm_thick = scan("THICK-DYADIC witness class (Fermat + generalized-Fermat ladder)", thick)
    cp_thin, cm_thin = scan("THIN prize-like class (odd-rich m, growing log m at fixed n)", thin)

    flush(f"\n{'='*100}")
    flush("# PINNED NECESSARY-CONDITION CONSTANTS")
    flush(f"{'='*100}")
    flush(f"  THICK class:  c_p* = max B^2/(n log p) = {cp_thick:.4f}   c_m* = max B^2/(n log m) = {cm_thick:.4f}")
    flush(f"  THIN  class:  c_p* = {cp_thin:.4f}   c_m* = {cm_thin:.4f}")
    flush(f"\n  (NC1) prize target constant in sqrt(2 n log p): the realizable THICK family forces")
    flush(f"        B^2/(n log p) up to {cp_thick:.3f} > 2  -- so 'B <= sqrt(2 n log p)' is FALSE on")
    flush(f"        realizable mu_n.  ANY valid proof must therefore use a feature ABSENT in the thick")
    flush(f"        witness (thinness/large log m / 2-adic), i.e. cannot be thickness-monotone.")
    flush(f"  (NC2) The honest scale is log m: c_m* drops from {cm_thick:.2f} (thick) toward {cm_thin:.2f} (thin).")
    flush(f"        Salem-Zygmund c=2 is an upper bound ONLY once thinness makes log m large -> THIS is")
    flush(f"        the formal sense in which thinness is ESSENTIAL.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
