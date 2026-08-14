#!/usr/bin/env python3
"""
probe_p2_softceiling_excess_sign.py  (#444 — P2: prove No-Excess UNCONDITIONALLY)

GOAL. The di Benedetto beat (0.9583 at beta=4) needs t_2<=2, t_3<=3, i.e. the SOFT CEILINGS
  E_2^{Fp} <= C2 * n^2  and  E_3^{Fp} <= C3 * n^3   at the prize scale p ~ n^4.
NOT the exact-equality faithfulness E_r^{Fp} == E_r^0. The probe_charp_faithfulness_depth_law
measures EQUALITY (which fails at adversarial primes). This probe measures the INEQUALITY:
the SIGN and SIZE of the char-p EXCESS A_r := E_r^{Fp} - E_r^0, and whether the realized
exponent t_r = log_n(E_r^{Fp}) stays <= r.

KEY QUESTION (decides whether P2 is reachable):
  When faithfulness EQUALITY breaks (E_r^{Fp} != E_r^0), is the excess A_r:
    (a) NEGATIVE/zero  -> soft ceiling STILL holds, di Benedetto beat survives -> PROMISING
    (b) POSITIVE but o(n^r) -> exponent t_r still <= r -> beat survives in EXPONENT
    (c) POSITIVE and >= constant*n^r -> t_r pushed ABOVE r -> beat BREAKS -> di Benedetto unconditional FALSE

The char-p energy is a COUNT of additive relations, so it can only GAIN solutions mod p
(extra wraparound coincidences) -> A_r >= 0 ALWAYS. So (a) is impossible; the question is (b) vs (c).

RULE-2 proper mu_n (n=2^mu, n|p-1, m=(p-1)/n>=2, p PRIME, NEVER n=p-1). p in prize band p~n^4.
RULE-1 pure-python EXACT integer counts => trivially axiom-clean.
RULE-6 sub-prize n (tractable); maps the law, does NOT prove forall-field at 2^30.
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
    print("="*108)
    print("P2 SOFT-CEILING EXCESS SIGN/SIZE:  A_r = E_r^{Fp} - E_r^0, and realized exponent t_r=log_n(E_r^{Fp})")
    print("di Benedetto needs t_2<=2, t_3<=3 at p~n^4 (NOT equality). Excess A_r>=0 always (extra wraparounds).")
    print("="*108)
    # E_2^0 = 3n^2-3n, E_3^0 = 15n^3-45n^2+40n
    for n in [16, 32, 64]:
        E20 = 3*n*n - 3*n
        E30 = 15*n**3 - 45*n*n + 40*n
        print(f"\nn={n}:  E_2^0={E20} (=3n^2-3n, t2_0={math.log(E20)/math.log(n):.4f})   "
              f"E_3^0={E30} (=15n^3-45n^2+40n, t3_0={math.log(E30)/math.log(n):.4f})")
        print(f"    {'p':>13} {'beta':>5} | {'E_2^Fp':>10} {'A_2':>8} {'t_2':>7} {'t2<=2?':>7} | "
              f"{'E_3^Fp':>12} {'A_3':>9} {'t_3':>7} {'t3<=3?':>7}")
        # scan the prize band beta in [3.5, 4.5], pick the WORST (largest excess) prime per band
        for (blo, bhi) in [(3.5, 3.65), (3.9, 4.1), (4.4, 4.6)]:
            ps = proper_band_primes(n, blo, bhi, 25 if n <= 32 else 12)
            if not ps: 
                print(f"    [{blo},{bhi}]: no proper prime"); continue
            # find worst (max A_2 and max A_3) over the band
            worst2 = None; worst3 = None
            for p in ps:
                mu = roots_modp(n, p)
                E2 = Ep(mu, p, 2)
                if worst2 is None or E2 > worst2[1]: worst2 = (p, E2)
            # report worst-A_2 prime's full r=2,3 line + also worst-A_3 prime
            for label, target in [("worstA2", worst2)]:
                p = target[0]; mu = roots_modp(n, p)
                E2 = Ep(mu, p, 2); E3 = Ep(mu, p, 3)
                A2 = E2 - E20; A3 = E3 - E30
                t2 = math.log(E2)/math.log(n) if E2 > 0 else 0
                t3 = math.log(E3)/math.log(n) if E3 > 0 else 0
                beta = math.log(p)/math.log(n)
                print(f"    {p:>13} {beta:>5.2f} | {E2:>10} {A2:>8} {t2:>7.4f} "
                      f"{'YES' if t2 <= 2.0001 else 'NO':>7} | "
                      f"{E3:>12} {A3:>9} {t3:>7.4f} {'YES' if t3 <= 3.0001 else 'NO':>7}", flush=True)
    print("\n" + "="*108)
    print("VERDICT: read whether t_2<=2 and t_3<=3 hold at the WORST prize-band prime.")
    print(" * If t_r EXCEEDS r at p~n^4: di Benedetto beat is UNCONDITIONALLY FALSE (excess crosses the floor).")
    print(" * If t_r stays <= r but A_r>0: equality fails but SOFT ceiling holds -> beat survives, P2 reachable.")
    print("="*108)

if __name__ == "__main__":
    main()
