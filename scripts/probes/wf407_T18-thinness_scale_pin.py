#!/usr/bin/env python3
"""wf407_T18-thinness_scale_pin.py  (#407 T18 — pin the CORRECT scale + the bootstrap break)

Two questions the thick-window measurement raises, answered EXACTLY:

Q1 (scale): the EVT law is  B ~ sqrt(c n log m),  m=(p-1)/n.  Three candidate
   "optimal" upper-bound scales appear in the literature/threads:
     (S_p)  B <= sqrt(2 n log p)         [the target T18 says is false]
     (S_m2) B <= sqrt(2 n log m)         [Salem-Zygmund / chaining, c=2]
     (S_m1) B <= sqrt(  n log m)         [bare-Gaussian c=1]
   We compute, for EXACT enumerations, the max over a large family of the ratio
   B/scale for each, and report WHICH scale is an upper bound (ratio<=1 always) and
   which is violated.  A necessary condition for a correct proof is: it must target a
   scale that is actually an upper bound; targeting a violated scale is logically dead.

Q2 (the B_inf <- B_{log n} Sidon-depth bootstrap break): the moment/Sidon method proves
   B from the even moments E_r(mu_n) up to r ~ log m (depth ~ log n at the prize). The
   bound it yields is  B <= (q E_r)^{1/2r}, optimized over r, = sqrt(2 n log m) IF the
   Gaussian energy E_r <= (2r-1)!! n^r holds up to r*=log m. The bootstrap "depth" is the
   largest r for which char-0 Gaussian energy transfers to char-p. We measure, at Fermat
   and diagonal, the SMALLEST scale sqrt(2 n log M) that actually upper-bounds B (i.e.
   solve for the effective log M_eff := B^2/(2n)) and compare to log m and log p. This
   M_eff is the "effective number of independent periods"; where M_eff > m the periods
   are MORE spread than m independent Gaussians (the bootstrap must over-shoot), where
   M_eff < m they are thinner. We report log M_eff / log m and / log p.

EXACT method = same coset transversal as the thick-window probe.
"""
import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import numpy as np


def all_periods_abs(p, n):
    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)
    sub = np.empty(n, dtype=np.int64); cur = 1
    for i in range(n):
        sub[i] = cur; cur = cur * gm % p
    m = (p - 1) // n
    twp = 2.0 * math.pi / p
    out = np.empty(m, dtype=np.float64)
    b = 1
    for j in range(m):
        prods = (b * sub) % p
        ang = twp * prods
        out[j] = math.hypot(np.cos(ang).sum(), np.sin(ang).sum())
        b = b * g % p
    return out


def report(p, n):
    a = all_periods_abs(p, n)
    B = float(a.max())
    m = (p - 1) // n
    lnp = math.log(p)
    lnm = math.log(m) if m > 1 else float('nan')
    logMeff = B * B / (2.0 * n)            # B = sqrt(2 n logMeff)  => logMeff = B^2/(2n)
    return dict(B=B, m=m, lnp=lnp, lnm=lnm, logMeff=logMeff,
                r_Sp=B / math.sqrt(2 * n * lnp),
                r_Sm2=(B / math.sqrt(2 * n * lnm)) if m > 1 else float('nan'),
                r_Sm1=(B / math.sqrt(n * lnm)) if m > 1 else float('nan'))


def main():
    flush = lambda *a: print(*a, flush=True)
    flush("#" * 100)
    flush("# T18 scale-pin: which 'optimal' scale is a TRUE upper bound on B? + effective M.")
    flush("#" * 100)

    # ---- gather an EXACT family: Fermat dyadic + a diagonal of non-dyadic primes ----
    fam = []   # (label, p, n)
    p = 65537
    for mu in range(1, 16):
        n = 1 << mu
        if (p - 1) // n >= 2:
            fam.append(("F65537", p, n))
            fam[-1] = ("F65537", p, n)
    # rebuild cleanly
    fam = [("F65537", 65537, 1 << mu) for mu in range(1, 16)]
    # diagonal non-dyadic
    for n in (16, 32, 64):
        used = set()
        for beta in (1.6, 1.9, 2.2, 2.6, 3.0, 3.5, 4.0):
            base = int(round(n ** beta));  base -= base % n; base += 1
            if base > 2_000_000: continue
            p2, t = base, 0
            while t < 1_000_000 and p2 < 3_000_000:
                if p2 > 3 and is_prime(p2) and odd_part((p2 - 1)//n) > 1 and p2 not in used:
                    used.add(p2); fam.append((f"diag{n}", p2, n)); break
                p2 += n; t += 1

    flush(f"\n{'label':>8} {'p':>9} {'n':>6} {'beta':>5} {'m':>7} "
          f"{'B/Sp':>7} {'B/Sm2':>7} {'B/Sm1':>7} {'logMeff':>8} {'logMeff/logm':>13} {'logMeff/logp':>13}")
    maxes = dict(Sp=0.0, Sm2=0.0, Sm1=0.0)
    rows = []
    for label, pp, nn in fam:
        d = report(pp, nn)
        beta = math.log(pp) / math.log(nn)
        rows.append((label, pp, nn, beta, d))
        maxes['Sp'] = max(maxes['Sp'], d['r_Sp'])
        if d['m'] > 1:
            maxes['Sm2'] = max(maxes['Sm2'], d['r_Sm2'])
            maxes['Sm1'] = max(maxes['Sm1'], d['r_Sm1'])
        rmm = d['logMeff']/d['lnm'] if d['m'] > 1 else float('nan')
        rmp = d['logMeff']/d['lnp']
        flush(f"{label:>8} {pp:>9} {nn:>6} {beta:>5.2f} {d['m']:>7} "
              f"{d['r_Sp']:>7.3f} {d['r_Sm2']:>7.3f} {d['r_Sm1']:>7.3f} "
              f"{d['logMeff']:>8.3f} {rmm:>13.3f} {rmp:>13.3f}")

    flush(f"\n{'='*100}")
    flush("# Family-wide MAX of B/scale  (>1 => that scale is NOT a valid upper bound on this family):")
    flush(f"   max B/sqrt(2n log p)  = {maxes['Sp']:.4f}   (target T18) "
          f"{'VIOLATED -> dead scale' if maxes['Sp']>1 else 'holds'}")
    flush(f"   max B/sqrt(2n log m)  = {maxes['Sm2']:.4f}   (Salem-Zygmund c=2) "
          f"{'VIOLATED' if maxes['Sm2']>1 else 'holds'}")
    flush(f"   max B/sqrt(  n log m) = {maxes['Sm1']:.4f}   (bare Gaussian c=1) "
          f"{'VIOLATED' if maxes['Sm1']>1 else 'holds'}")
    flush(f"\n  Reading: a NECESSARY CONDITION for a valid proof is targeting a scale whose")
    flush(f"  family-max ratio is <=1. The data pins which constant c in sqrt(c n log m) survives.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
