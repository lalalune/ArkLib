# n=64 race check (rule-6 adversarial: does rho>1 actually arrive at n=64, = a DISPROOF of A_r<=Wick?).
# E0_ring(64,r) is a Z^32 lattice convolution; tractable for small r. Ep(mu64,p,r) mod-p conv fine.
import math, time
from probe_407_anom_worst_rtraj_n32 import (Ep, E0_ring, wick, roots_modp, is_prime,
                                            find_worst_inwindow_bad_prime, rstar)
n=64
t0=time.time()
# bad primes onset at LOW r for n=64 (onset table: n=32 reaches window at r=2; n=64 even lower). anchor r=2.
best, scanned, bad = find_worst_inwindow_bad_prime(n, 2, beta_lo=4.0, n_primes_scan=2500)
print(f"n=64 anchor r=2: scanned {scanned}, {bad} bad, elapsed {time.time()-t0:.0f}s")
if best is None:
    print("no in-window bad prime at anchor r=2; trying r=3"); best,scanned,bad=find_worst_inwindow_bad_prime(n,3,4.0,2500)
if best:
    p=best[0]; beta=math.log(p)/math.log(n); mu=roots_modp(n,p)
    print(f"n=64 worst bad prime p={p} beta={beta:.3f} index={(p-1)//n} r*={rstar(p)}")
    print(f"  {'r':>3} {'Anom_r':>18} {'H_r':>20} {'rho':>10} {'A_r/Wick':>10} {'TGT':>6}")
    for r in range(2, 5):  # r=2,3,4 only (E0_ring(64,4) Z^32 conv is the tractable ceiling)
        tr=time.time(); Epp=Ep(mu,p,r); E0=E0_ring(n,r); W=wick(n,r); anom=Epp-E0
        nbp=(n**(2*r))/p; H=(W-E0)+nbp; rho=anom/H if H>0 else float('inf')
        A_r=Epp-nbp; aw=A_r/W; tgt="OK" if aw<=1 else "CRACK"
        print(f"  {r:>3} {anom:>18} {H:>20.2f} {rho:>10.5f} {aw:>10.5f} {tgt:>6}  ({time.time()-tr:.0f}s)")
