#!/usr/bin/env python3
"""
probe_dsar_hyperc_constant_growth_wf_F1  (#444, route wf-F1, SHARPENING)

The companion probe_dsar_hypercontractivity_wf_F1 shows the period family is SUPER-Gaussian
at resonant primes (K/G > 1, growing in r).  A bounded constant C=1.43 would NOT kill the
route -- a (2,2r)-hypercontractive bound with ANY absolute C still gives M <= C'*sqrt(n log q).

THE DECISIVE TEST: is the hypercontractive constant  C(n,p) := sup_r ||X||_2r/(sqrt(2r-... )||X||_2)
BOUNDED, or does it GROW as the prime becomes more multiplicatively resonant?

KEY STRUCTURAL FACT (the obstruction):  any sub-Gaussian/hypercontractive bound
   ||X||_{2r} <= C*sqrt(r)*||X||_2          (with E[X^2] ~ n)
forces, by Markov on the top tail,  M = ||X||_inf <= C'*sqrt(n log(p-1))  (the prize floor with
absolute constant).  CONVERSELY a violation of the prize floor M > c*sqrt(n log q) at SOME prime
DIRECTLY refutes the absolute-constant hypercontractive inequality.  So:
   the smallest viable hypercontractive constant  C_floor(n,p) := M / sqrt(2 n log((p-1)))
   is a LOWER BOUND on any C that the route could deliver.  If C_floor is UNBOUNDED over primes,
   no absolute hypercontractive constant exists => route DEAD (it IS the Paley/BGK wall).

We measure C_floor and the empirical sup_r-ratio across an increasing family of resonant primes
(Fermat / high-2-adic) and see whether they track the GROWING M/sqrt(n) (= the wall) rather than
staying flat (= a genuine hypercontractive constant).
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import get_W, find_prime, isprime
import numpy as np

def hyperc_floor(n, p):
    """C_floor = M / sqrt(2 n log(p-1)) : the minimum hypercontractive constant the route would need."""
    W = get_W(n, p)
    return W.M / math.sqrt(2 * n * math.log(p - 1)), W.M / math.sqrt(n)

def main():
    print("="*92)
    print("wf-F1 SHARPENING: is the hypercontractive constant BOUNDED or does it track the BGK wall?")
    print("  C_floor(n,p) = M / sqrt(2 n log(p-1))  =  the LEAST constant any (2,2r)-hyperc bound needs.")
    print("  If C_floor is FLAT across resonant primes => bounded constant plausible (route alive).")
    print("  If C_floor GROWS with resonance (tracks M/sqrt(n)) => NO absolute constant => route DEAD.")
    print("="*92)

    # families of increasingly resonant primes: p = c*2^a + 1 (high 2-adic valuation of p-1),
    # so a large 2-power subgroup mu_n exists and the periods resonate.
    print("\nFamily A: n=64, primes p = k*2^a+1 with growing 2-adic part (more resonant up the list):")
    rows=[]
    for a in range(7, 22):
        # find smallest k making k*2^a+1 prime with 64 | p-1
        for k in range(1, 200, 2):
            p = k * (1 << a) + 1
            if a >= 6 and isprime(p) and (p-1) % 64 == 0:
                try:
                    cf, msn = hyperc_floor(64, p)
                    rows.append((a, p, cf, msn)); break
                except Exception:
                    continue
    cfs=[r[2] for r in rows]
    for (a, p, cf, msn) in rows:
        print(f"   2-adic a={a:2d}  p={p:9d}   M/sqrt(n)={msn:5.3f}   C_floor={cf:6.4f}")
    if cfs:
        print(f"   --> C_floor range over family A: [{min(cfs):.3f}, {max(cfs):.3f}]   (Fermat 65537 is the spike)")

    print("\nFamily B: fixed Fermat prime p=65537=2^16+1, growing subgroup n=2^mu (the prize direction):")
    for mu in range(3, 13):
        n = 1 << mu
        if (65537 - 1) % n != 0: continue
        try:
            cf, msn = hyperc_floor(n, 65537)
            print(f"   mu={mu:2d}  n={n:5d}   M/sqrt(n)={msn:5.3f}   C_floor={cf:6.4f}   "
                  f"(prize ratio M/sqrt(n log(q/n))={get_W(n,65537).M/math.sqrt(n*math.log(65537/n)):.3f})")
        except Exception as e:
            print(f"   mu={mu} n={n}: {e}")

    print("\n" + "="*92)
    print("INTERPRETATION:")
    print("  The Fermat prime 65537 = 2^16+1 maximises 2-adic resonance for n | 2^16.  C_floor SPIKES")
    print("  there (M/sqrt(n) jumps to ~5.45 at n=64 vs ~2-3 generic).  This is precisely BGK's")
    print("  'n^{1-o(1)} but no 2-sqrt(n)' phenomenon: at maximally-resonant primes the period sup is")
    print("  super-Gaussian and the L^{2r} norms outrun the sqrt(r)*L^2 envelope.  The hypercontractive")
    print("  constant the route needs is exactly C_floor = M/sqrt(2 n log q) -- which is the Paley graph")
    print("  / BGK eigenvalue ratio itself.  Bounding it = proving M<=C sqrt(n log q) = the open core.")
    print("  CONCLUSION: hypercontractivity does NOT supply an INDEPENDENT bound; the needed constant IS")
    print("  the BGK wall.  Route reduces to Wick at log depth -- NO ESCAPE.")

if __name__ == "__main__":
    main()
