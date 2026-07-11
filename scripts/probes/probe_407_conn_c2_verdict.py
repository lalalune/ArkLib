#!/usr/bin/env python3
"""
#407 CONNECTION C2 — CONSOLIDATED VERDICT.

Three measured facts, assembled into the answer to C2(a)(b)(c).

FACT 1 (moment crossover r*).  At prize p~n^4 (beta=4), the per-moment char-p anomaly
  #spurious_r = E_r(F_p) - E_r^0(ring) is EXACTLY 0 for r<=3 (=beta-1) and turns on at
  r=4 (=beta): ratio #spurious_r/(n^{2r}/p) jumps 0,0,0.81 at r=2,3,4 (mu=6).
  Confirmed mu=6,7 (r=2,3 clean); r* tracks beta (n=32: clean to r~beta, climbs to ~1
  by r~beta+1). So r* ≈ beta (to beta+1).  [probe_407_conn_c2_crossover_scan]

FACT 2 (count-lane config depth r_count).  delta* is set by the worst-case agreement set
  of size |S| = rho*n (a FIXED FRACTION of n), so the count-lane depth is
  r_count = rho*n/m  — which GROWS LINEARLY IN n (mu=6:14, mu=30:2.3e8), unbounded.

FACT 3 (saturation onset = where the count lane can go spurious).  The count-lane
  spurious configs obey "spurious => saturated" (verified 400 non-sat primes: ZERO
  spurious except one deeply-saturated p=17 case). Saturation = |Sigma_r| >= p.
  The TRUE distinct-sumset |Sigma_r| crosses p=n^4 at a SMALL onset r ~ beta+1..beta+2
  (n=8:10, n=16:7, n=32:6, n=64:5), roughly CONSTANT (slightly decreasing toward beta),
  NOT growing with n.  [probe_407_conn_c2_gap_vs_generic + true-sigma scan]

VERDICT.  The count-lane depth r_count = rho*n/m GROWS LINEARLY in n; the moment crossover
  r* AND the saturation onset both stay ~ beta (constant). So:
     r_count  >>  r*  ≈  saturation-onset  ≈  beta.
  The worst-case count-lane config size is FAR ABOVE the crossover. At that size the prize
  prime is DEEPLY SATURATED (|Sigma_{r_count}| >> p by ~2^{Theta(n)}), so the
  "spurious=>saturated => safe" escape FAILS exactly at the prize config size.
  => C2(b): the count lane is ABOVE the crossover. It RE-HITS the BGK/moment wall.
  => C2(c): the excess is NOT provably 0 at the prize config size by a finite low-degree
     resultant; the height/norm certificate p<=L^{n/2} is VACUOUS at L=rho*n
     (p=n^4 << (rho n)^{n/2}).  The clean "single q-independent count" picture is a
     SMALL-config-size artifact; it does not survive to the prize config depth.
"""
import math

def main():
    print("="*92)
    print("C2 VERDICT — count-lane depth r_count vs moment crossover r* vs saturation onset")
    print("="*92)
    print(f"  {'mu':>3} {'n':>11} {'r*~beta':>8} {'sat-onset~':>11} {'r_count=rho n/m':>16} "
          f"{'r_count/r*':>11} {'log2(p)':>8} {'log2 L^(n/2)':>13} {'cert vacuous?':>13}")
    # measured sat-onset for small n: n=8:10,16:7,32:6,64:5 -> fit ~ const near beta+1..2
    measured_onset = {8:10,16:7,32:6,64:5}
    for mu in [3,4,5,6,8,10,12,16,20,24,30]:
        n=2**mu; rho=7/16; m=2; beta=4.0
        rstar=beta
        onset = measured_onset.get(n, beta+1)  # ~constant ~ beta+1 for large n
        rcount=rho*n/m
        L=rho*n
        log2p=beta*mu
        log2_height=(n/2)*math.log2(max(L,2))
        vac = 'YES' if log2_height>log2p else 'no'
        print(f"  {mu:>3} {n:>11} {rstar:>8.0f} {onset:>11} {rcount:>16.0f} "
              f"{rcount/rstar:>11.1f} {log2p:>8.0f} {log2_height:>13.0f} {vac:>13}")
    print()
    print("READING: r_count grows ~ n/4 while r* and saturation-onset stay ~ beta (const).")
    print("  The count lane's worst case sits a factor ~n ABOVE the crossover => re-hits BGK.")
    print("  The norm/height certificate p<=L^(n/2) is vacuous for all mu>=4 => NO finite")
    print("  low-degree resultant proves excess=0 at the prize config size. C2(c) answer: none exists")
    print("  by elementary means; the residual is the recognized char-p energy transfer (BGK).")

if __name__=="__main__":
    main()
