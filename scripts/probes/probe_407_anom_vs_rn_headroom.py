# #407 — the CLEAN unified open inequality: A_r<=Wick <=> Anom_r <= (r/n)*Wick.
# Combines 0xSolace's exact char-0 margin E_r^(0)/Wick = 1 - r/n + O(1/n^2) (push 44234dc3d) with my
# anomaly growth: A_r/Wick = E_r^(p)/Wick - n^{2r}/(p*Wick) = (E0/Wick) + (Anom_r/Wick) - n^{2r}/(p Wick).
# Since E0/Wick = 1 - r/n + O(1/n^2) and n^{2r}/(p Wick) is tiny (p>=n^4), to leading order:
#   A_r<=Wick  <=>  Anom_r <= (r/n)*Wick + n^{2r}/p  =:  Hrn   (the r/n headroom + DC term).
# Define kappa_r := Anom_r / ((r/n)*Wick). Carrier (to leading order) holds iff kappa_r <= ~1.
# This is the SHARPEST reformulation: the prize <=> the bad-prime anomaly stays within the r/n char-0 margin.
import math
from probe_407_anom_worst_rtraj_n32 import (Ep, E0_ring, wick, roots_modp, is_prime,
                                            find_worst_inwindow_bad_prime, rstar)

def run(n, r_anchor, beta_lo, n_scan, r_cap=5):
    best,scanned,bad=find_worst_inwindow_bad_prime(n,r_anchor,beta_lo=beta_lo,n_primes_scan=n_scan)
    if best is None:
        print(f"n={n}: no in-window bad prime (anchor r={r_anchor})"); return None
    p=best[0]; beta=math.log(p)/math.log(n); rs=min(rstar(p),r_cap); mu=roots_modp(n,p)
    print(f"\nn={n} worst bad prime p={p} beta={beta:.3f} index={(p-1)//n} (proper, not n=q-1)")
    print(f"  {'r':>3} {'Anom_r':>16} {'(r/n)Wick':>16} {'kappa=Anom/(rn Wick)':>20} {'E0/Wick':>9} {'A_r/Wick':>9}")
    peak=0; peakr=None
    for r in range(2,rs+1):
        Epp=Ep(mu,p,r); E0=E0_ring(n,r); W=wick(n,r); anom=Epp-E0
        rnW=(r/n)*W; kappa=anom/rnW if rnW>0 else float('inf')
        e0w=E0/W; aw=(Epp-(n**(2*r))/p)/W
        if kappa>peak: peak=kappa; peakr=r
        print(f"  {r:>3} {anom:>16} {rnW:>16.2f} {kappa:>20.5f} {e0w:>9.5f} {aw:>9.5f}")
    print(f"  => peak kappa = {peak:.5f} @ r={peakr}  (carrier ~holds iff kappa<=1)")
    return {"n":n,"beta":beta,"peak_kappa":peak,"peakr":peakr}

if __name__=="__main__":
    res=[]
    for (n,ra,bl,ns) in [(16,4,4.0,600),(32,3,4.0,1500),(64,2,4.0,3000)]:
        r=run(n,ra,bl,ns)
        if r: res.append(r)
    print("\n==== kappa_r = Anom_r / ((r/n)*Wick) at the worst bad prime ====")
    for r in res: print(f"  n={r['n']:>3} beta={r['beta']:.3f} peak_kappa={r['peak_kappa']:.5f} @r={r['peakr']}")
    if len(res)>=2:
        print(f"  => trend: {'RISING (anomaly outgrows r/n margin -> carrier breaks)' if res[-1]['peak_kappa']>res[0]['peak_kappa'] else 'stable/falling'}")
