#!/usr/bin/env python3
"""
#407 — the HEADROOM-vs-ANOMALY race at the worst in-window bad prime, across n.

MOTIVATION (from caab0afb9): at n=32 the carrier A_r<=Wick survives ONLY via the growing Wick-E0
headroom (the sufficient proxy Anom_r<=n^{2r}/p died 16x/octave). So the route's asymptotic fate is the
RACE between the anomaly Anom_r and the headroom. Make that race explicit.

EXACT ALGEBRA:  A_r = E_r^(p) - n^{2r}/p = (E0 + Anom_r) - n^{2r}/p.
  A_r <= Wick  <=>  Anom_r <= (Wick - E0) + n^{2r}/p =: H_r   (the TRUE headroom).
  Define the RACE RATIO  rho_r := Anom_r / H_r.   Carrier holds iff rho_r <= 1.
  (Distinct from the proxy ratio Anom_r/(n^{2r}/p) which IGNORES the Wick-E0 term — that's why the proxy
   is too strong and dies; H_r includes the char-0 floor headroom.)

QUESTION: at the worst in-window bad prime, does rho_r stay comfortably < 1 (route robust) or does it
creep toward 1 as n grows (knife-edge closing => route in doubt at the prize)? Track rho_r(n,r) for
n=8,16,32 at each n's worst bad prime, over r=2..r_cap. Report the PEAK rho_r per n (the binding rung).

RULE-2 proper mu_n, p>=n^4, never n=q-1. RULE-1 pure-python exact => axiom-clean. RULE-6 sub-prize p;
maps the race at accessible scale, does NOT prove the asymptotic (BGK). No CORE closure.
"""
import math
from probe_407_anom_worst_rtraj_n32 import (Ep, E0_ring, wick, roots_modp, is_prime,
                                            find_worst_inwindow_bad_prime, rstar)

def race_for_n(n, r_anchor, beta_lo, n_scan, r_cap=6):
    best, scanned, bad = find_worst_inwindow_bad_prime(n, r_anchor, beta_lo=beta_lo, n_primes_scan=n_scan)
    if best is None:
        print(f"n={n}: NO in-window bad prime (anchor r={r_anchor}, scan {scanned})"); return None
    p = best[0]; beta = math.log(p)/math.log(n); rs = min(rstar(p), r_cap)
    mu = roots_modp(n, p)
    print(f"\nn={n}: worst bad prime p={p} beta={beta:.3f} index={(p-1)//n} r*={rstar(p)} cap={rs}")
    print(f"  {'r':>3} {'Anom_r':>16} {'H_r=(Wick-E0)+n2r/p':>22} {'rho=Anom/H':>11} {'A_r/Wick':>10}")
    peak = 0.0; peak_r = None
    for r in range(2, rs+1):
        Epp = Ep(mu, p, r); E0 = E0_ring(n, r); W = wick(n, r)
        anom = Epp - E0
        nbp = (n**(2*r))/p
        H = (W - E0) + nbp
        rho = anom / H if H > 0 else float('inf')
        A_r = Epp - nbp; aw = A_r/W
        if rho > peak: peak = rho; peak_r = r
        print(f"  {r:>3} {anom:>16} {H:>22.2f} {rho:>11.5f} {aw:>10.5f}")
    print(f"  => PEAK race ratio rho = {peak:.5f} at r={peak_r}  (carrier holds iff rho<=1)")
    return {"n": n, "p": p, "beta": beta, "peak_rho": peak, "peak_r": peak_r}

if __name__ == "__main__":
    results = []
    # n=8: bad primes onset higher r; n=16/32 as in the trajectory probe
    for (n, r_anchor, beta_lo, n_scan) in [(8, 6, 4.0, 600), (16, 4, 4.0, 600), (32, 3, 4.0, 1500)]:
        res = race_for_n(n, r_anchor, beta_lo, n_scan)
        if res: results.append(res)
    print("\n==== RACE SUMMARY: peak Anom_r/H_r at the worst in-window bad prime ====")
    print(f"  {'n':>4} {'beta':>7} {'peak_rho':>10} {'peak_r':>7}")
    for r in results:
        print(f"  {r['n']:>4} {r['beta']:>7.3f} {r['peak_rho']:>10.5f} {r['peak_r']:>7}")
    if len(results) >= 2:
        trend = "RISING toward 1 (knife-edge closing)" if results[-1]['peak_rho'] > results[0]['peak_rho'] else "stable/falling (route robust)"
        print(f"  => peak race ratio across n: {trend}")
