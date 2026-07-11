#!/usr/bin/env python3
"""
probe_p2_constant_ceiling.py  (#444 — P2: No-Excess as CONSTANT-FACTOR soft ceiling)

CORRECTION to probe_p2_softceiling_excess_sign: di Benedetto's t_2=2 means E_2=Theta(n^2)
(CONSTANT times n^2, the '3' in 3n^2 is absorbed in o(1) of the exponent). So the real soft
ceiling is the CONSTANT c_r := E_r^{Fp}/n^r staying BOUNDED (and, for the BEAT, c_r <= the
char-0 Wick constant (2r-1)!! up to lower order: c_2<=3, c_3<=15).

This probe measures, at the WORST (max-excess) proper prize-band prime:
  c_2^{Fp} = E_2^{Fp}/n^2  vs char-0 limit 3,   c_3^{Fp} = E_3^{Fp}/n^3 vs 15
  and the RELATIVE excess A_r/E_r^0 (does it -> 0, stay bounded, or grow with n?).

The di Benedetto saving formula (10-2t3-t2/2)/72 uses the EXPONENTS t2,t3; a bounded constant
inflation (c_2: 3 -> 3+eps) does NOT change t_2=2, so the BEAT (exponent 0.9583) is robust to
constant inflation. The beat BREAKS only if the relative excess A_r/n^r GROWS (t_r > r).

We scan n=16..128, take the worst prime in [n^3.5, n^4.5], and FIT A_r/n^r vs n.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring, roots_modp, is_prime

def proper_band_primes(n, blo, bhi, cap):
    lo = max(int(n**blo), n**3 + 1); hi = int(n**bhi)
    out = []; m = max(2, lo//n)
    while m*n + 1 <= hi and len(out) < cap:
        p = m*n + 1
        if p >= lo and p > n**3 and is_prime(p): out.append(p)
        m += 1
    return out

def main():
    print("="*104)
    print("P2 CONSTANT-FACTOR CEILING: c_r = E_r^{Fp}/n^r at WORST prize-band prime (beta in [3.5,4.5]).")
    print("di Benedetto t_2=2,t_3=3 hold iff c_2,c_3 BOUNDED. char-0 limits: c_2->3, c_3->15.")
    print("Beat survives if relative excess A_r/E_r^0 stays bounded (does NOT need to ->0).")
    print("="*104)
    print(f"{'n':>5} | {'worst p':>13} {'beta':>5} | {'c2^Fp':>8} {'A2/E2^0':>9} | "
          f"{'c3^Fp':>8} {'A3/E3^0':>9} {'A3/n^3':>9}")
    rows = []
    for n in [16, 32, 64, 128]:
        E20 = 3*n*n - 3*n; E30 = 15*n**3 - 45*n*n + 40*n
        ps = proper_band_primes(n, 3.5, 4.5, 40 if n <= 64 else 8)
        if not ps:
            print(f"{n:>5} | (no proper prime)"); continue
        # worst = max E_3^{Fp} (deepest excess) over band
        best = None
        for p in ps:
            mu = roots_modp(n, p)
            E3 = Ep(mu, p, 3)
            if best is None or E3 > best[1]:
                E2 = Ep(mu, p, 2)
                best = (p, E3, E2)
        p, E3, E2 = best
        beta = math.log(p)/math.log(n)
        c2 = E2/n**2; c3 = E3/n**3
        a2rel = (E2-E20)/E20; a3rel = (E3-E30)/E30; a3n3 = (E3-E30)/n**3
        print(f"{n:>5} | {p:>13} {beta:>5.2f} | {c2:>8.4f} {a2rel:>9.5f} | "
              f"{c3:>8.4f} {a3rel:>9.5f} {a3n3:>9.4f}", flush=True)
        rows.append((n, c2, c3, a3rel, a3n3))
    print("\nTREND: c2,c3 vs char-0 (3,15); relative excess A3/E3^0 vs n.")
    print(" If c3 stays near 15 and A3/E3^0 -> 0 or bounded: t_3=3 holds, beat ROBUST.")
    print(" If c3 GROWS with n: t_3>3, beat BREAKS.")
    for (n,c2,c3,a3rel,a3n3) in rows:
        print(f"   n={n:>4}: c2={c2:.4f} c3={c3:.4f}  A3/E3^0={a3rel:.6f}  A3/n^3={a3n3:.4f}")
    print("="*104)

if __name__ == "__main__":
    main()
