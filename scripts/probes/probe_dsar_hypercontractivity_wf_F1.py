#!/usr/bin/env python3
"""
probe_dsar_hypercontractivity_wf_F1  (#444, route wf-F1)

ROUTE UNDER TEST: HYPERCONTRACTIVITY / SUB-GAUSSIAN on the period family.
   Does X_b := |eta_b| (b in F_p^*) have (2,2r)-hypercontractive / sub-Gaussian
   moment growth  ||X||_{2r} <= C*sqrt(r)*||X||_2  for an ABSOLUTE constant C?
   This is EXACTLY the Wick/sub-Gaussian bound that would give M <= sqrt(2 n log q):
       E_{b}[ X^{2r} ] <= (2r-1)!! * (E_b[X^2])^r        (sub-Gaussian moments, proxy = E[X^2]=n)
   <=> ||X||_{2r}/||X||_2  <=  ((2r-1)!!)^{1/2r} ~ sqrt(2r/e) = sqrt(r)*sqrt(2/e).

   The probability space is UNIFORM over b in F_p^* ( = E_r / second-moment normalisation:
   E_b[X^{2r}] = (1/(p-1)) * sum_{b!=0} |eta_b|^{2r} = (p E_r - n^{2r})/(p-1) ).

WHAT THE PROBE MEASURES (exact FFT spectra; cross-checked by definition):
   K(r) := ||X||_{2r} / ||X||_2      (the hypercontractive ratio)
   compared against the SUB-GAUSSIAN ENVELOPE  G(r) := ((2r-1)!!)^{1/2r}  (the Wick target).
   If  K(r) <= C * G(r)  with C ~ 1 uniformly in (n, p, r), the route is ALIVE (sub-Gaussian).
   If  K(r) / G(r)  GROWS with r at a resonant prime, the family is SUPER-Gaussian:
   NO hypercontractive constant exists => route DEAD, collapses to BGK at log depth.

   Also reports the per-frequency consumer:  M / sqrt(n log(p/n))  (the prize ratio),
   and the moment-method prediction  min_r (p*E_r)^{1/2r} / sqrt(n log(p/n)).
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import get_W, find_prime
import numpy as np

def double_fact_odd(r):
    df = 1.0
    for j in range(1, 2*r, 2):
        df *= j
    return df

def analyze(n, p, rmax=12):
    W = get_W(n, p)
    mag2 = W.mag2[1:]                 # |eta_b|^2 over b != 0   (length p-1)
    L2sq = mag2.mean()               # E_b[X^2]  = (p E_1 - n^2)/(p-1) ~ n
    L2 = math.sqrt(L2sq)
    M = W.M
    rows = []
    for r in range(1, rmax+1):
        # E_b[ X^{2r} ] uniform over b!=0
        m2r = (mag2.astype(np.float64) ** r).mean()
        L2r = m2r ** (1.0/(2*r))                  # ||X||_{2r}
        K = L2r / L2                              # hypercontractive ratio
        G = double_fact_odd(r) ** (1.0/(2*r))     # sub-Gaussian (Wick) envelope ~ sqrt(2r/e)
        rows.append((r, K, G, K/G))
    return W, M, L2, rows

def main():
    print("="*100)
    print("wf-F1 HYPERCONTRACTIVITY / SUB-GAUSSIAN test:  K(r)=||X||_2r/||X||_2  vs  Wick envelope G(r)=((2r-1)!!)^{1/2r}")
    print("  Route ALIVE iff  C := sup_r K(r)/G(r)  is bounded (sub-Gaussian).  DEAD if K/G grows (super-Gaussian).")
    print("="*100)

    # generic + the known resonant primes (Fermat F_16 = 65537 is the worst measured)
    cases = []
    for n in (16, 32, 64, 128, 256):
        for idx in (16, 256, 1024):
            p = find_prime(n, idx)
            if p: cases.append((n, p))
    # explicit resonant / Fermat
    cases += [(64, 65537), (128, 65537), (256, 65537), (16, 65537), (32, 65537)]
    # dedup
    seen=set(); cc=[]
    for c in cases:
        if c in seen: continue
        seen.add(c); cc.append(c)

    worst_C = 0.0; worst_at = None
    grows = []
    for (n, p) in cc:
        try:
            W, M, L2, rows = analyze(n, p)
        except Exception as e:
            print(f"  skip n={n} p={p}: {e}"); continue
        prize = M / math.sqrt(n * math.log(p / n))
        KG = [kg for (_,_,_,kg) in rows]
        Cn = max(KG)
        # is K/G monotonically growing (super-Gaussian signature)?
        trend = KG[-1] - KG[0]
        if Cn > worst_C: worst_C = Cn; worst_at = (n, p)
        if trend > 0.05: grows.append((n, p, trend, KG[0], KG[-1]))
        flag = "SUPER-GAUSSIAN(grows)" if trend > 0.05 else ("flat" if abs(trend)<0.05 else "sub")
        print(f"\nn={n:4d} p={p:6d}  M/sqrt(n)={M/math.sqrt(n):.3f}  prize M/sqrt(n log(p/n))={prize:.3f}  "
              f"sup_r K/G={Cn:.3f}  trend(K/G,r=1->12)={trend:+.3f}  [{flag}]")
        print("    r :  K(r)=||X||_2r/||X||_2   G(r)=Wick env    K/G")
        for (r, K, G, kg) in rows:
            mark = "  <== K/G>1.1" if kg > 1.1 else ""
            print(f"   {r:2d} :     {K:8.4f}            {G:7.4f}     {kg:6.3f}{mark}")

    print("\n" + "="*100)
    print(f"GLOBAL sup over all (n,p,r) of  K(r)/G(r)  =  {worst_C:.4f}   at  {worst_at}")
    if grows:
        print("SUPER-GAUSSIAN cases (K/G GROWS with r => NO absolute hypercontractive constant):")
        for (n,p,t,k0,k1) in grows:
            print(f"   n={n} p={p}:  K/G  {k0:.3f} (r=1)  ->  {k1:.3f} (r=12)   (+{t:.3f})")
    print("="*100)
    print("VERDICT LOGIC:")
    print("  * If K/G is FLAT in r and sup_r K/G ~ 1  => sub-Gaussian, route ALIVE (would prove Wick).")
    print("  * If K/G GROWS in r at resonant primes  => SUPER-Gaussian heavy tail, NO Bonami-Beckner")
    print("    constant exists; the (2,2r)-hypercontractive inequality FAILS; route reduces to the")
    print("    char-p deep-moment (BGK) wall it was meant to bypass.  => DECISIVE REFUTATION.")

if __name__ == "__main__":
    main()
