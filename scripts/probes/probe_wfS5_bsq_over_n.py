#!/usr/bin/env python3
"""wf-S5 (#444) — DECISIVE B^2/n turnover summary (driver / record of the Rust theta probes).

This Python file is the reproducibility RECORD of the exact folded-theta short-vector measurements
of the index-p sublattice L_P done in Rust (scripts/probes/rust/probe_wfS5_Bfit_largen.rs and the
deep-cap variants /tmp/wfS5_deep.rs, /tmp/wfS5_n64c12.rs). The numbers below are EXACT integer
meet-in-the-middle theta-shell counts at the prize regime beta=4, p == 1 mod n, worst-case prime.

DECISIVE FINDING (wf-S5):
  The lane's K = B^2 reading is LOOSE. The char-0 Wick value already carries n^r, so the spur-to-
  Wick ratio is governed by B^2/n, NOT B^2. Measured B^2/n stays BOUNDED BELOW 1 and the peak
  energy ratio R* = max_r cumTheta(2r)/Wick TURNS OVER and decays once the depth 2r passes the
  (n-growing) theta girth, because Wick (2r-1)!! n^r overtakes the geometric shell growth B^{2r}.

  This is PROVEN in Lean (axiom-clean): _wfS5BsqOverNTurnover.lean — if B^2 <= n then
  cumTheta(2r) <= A(2r+1) n^r (spur below the n^r factor), so E_r <= (1+A(2r+1)) Wick: a
  POLYNOMIAL-in-r multiplier, hence the asymptotic energy constant K=1 on the geometric corner.

  OPEN content sharpened: from "B bounded" (false — B grows) to "B^2 <= n" (measured true, the
  shell base squared stays below the subgroup order). The turnover is OBSERVED at n=16,32; at
  n=64 the exact-enumeration window (cap<=12) is too shallow to REACH the turnover depth (girth=8,
  peak expected ~r=7, needs cap~16), but B^2/n < 1 still holds.
"""

# EXACT folded-theta data (Rust meet-in-the-middle, no float in the counts). Format:
#   n : (worst prime, girth, shells[1..], asymptotic even-step B^2 = N_{w}/N_{w-2}, B^2/n, peak R*, peak r)
DATA = {
    8:  dict(p=4177,    girth=11, Bsq_cap=1.46,  Bsq_over_n=0.182, peakR=0.001, peakr=6,
             note="39/60 primes spur-free in range (girth>14): below-girth band wide"),
    16: dict(p=65537,   girth=5,  Bsq_cap=3.03,  Bsq_over_n=0.189, peakR=1.067, peakr=3,
             note="Fermat prime (worst). R turns over: 1.067->0.305->0.152->0.017 (r=3..6)"),
    32: dict(p=1048609, girth=8,  Bsq_cap=3.98,  Bsq_over_n=0.225, peakR=0.643, peakr=5,
             note="asymptotic N_14/N_12=7.2=B^2 -> B^2/n=0.225. R turns: 0.643->0.493->0.287 (r=5..7)"),
    64: dict(p=16777601,girth=8,  Bsq_cap=9.30,  Bsq_over_n=0.145, peakR=None,  peakr=None,
             note="cap=12 too shallow to reach turnover (R still rising r4..6); B^2/n=0.145<1 holds"),
}

def main():
    print("# wf-S5 B^2/n turnover summary — exact folded-theta of L_P, prize beta=4, p==1 mod n\n")
    print(f"{'n':>5} {'worst p':>11} {'girth':>6} {'B^2(cap)':>9} {'B^2/n':>7} {'peak R*':>8} {'r*':>3}  note")
    for n, d in sorted(DATA.items()):
        pr = f"{d['peakR']:.3f}" if d['peakR'] is not None else "  -  "
        rr = f"{d['peakr']}" if d['peakr'] is not None else "-"
        print(f"{n:>5} {d['p']:>11} {d['girth']:>6} {d['Bsq_cap']:>9.2f} {d['Bsq_over_n']:>7.3f} {pr:>8} {rr:>3}  {d['note']}")
    print()
    print("VERDICT: B^2/n bounded below 1 (0.14-0.23) across n=8..64; peak energy ratio R* bounded")
    print("  and turning over (n=16,32). The energy constant relative to char-0 Wick is poly(r), K=1")
    print("  asymptotically PROVIDED B^2 <= n at the prize scale (the open, measured-true input).")
    print("  Lean: _wfS5BsqOverNTurnover.lean (axiom-clean): B^2<=n => E_r <= (1+A(2r+1)) Wick.")

if __name__ == '__main__':
    main()
