#!/usr/bin/env python3
"""
SUP-NORM THINNESS GATE is beta-INVARIANT: the deeper Sidon depth at beta=5
(+8 vs +4 at beta=4, n=32) does NOT buy a better M_thin/M_neg-rand sup-norm ratio.

CONTEXT (the only live thinness-essential lead, #444 §7.2). The thin-Sidon
B_inf <- B_{log n} bootstrap: mu_n's Sidon DEPTH advantage genuinely GROWS with n
and is LARGER at beta=5 than beta=4 (thin r_min - random: +4 at n=32 beta=4, +8 at
n=32 beta=5). The named open wall: does growing depth CONVERT to a sup-norm saving?
probe_407_supnorm_thinness_gate.py found M_thin/M_neg-closed-random ~ 0.92 FLAT IN n
at beta=4 (depth->supnorm conversion fails). This probe asks the next sharp question:
is that gate ratio also FLAT IN beta, i.e. does the EXTRA depth at beta=5 buy anything?

REFRAME / why it matters: if the gate ratio SHRANK at beta=5 (where depth is +8),
that would be the live edge -- the bootstrap converting in the deeper regime. If it
stays flat (or worsens), the depth->supnorm failure is beta-ROBUST: the larger beta=5
Sidon depth is WASTED, tightening the §7.2 constraint.

RESULT (M_thin / M_neg-closed-random, two prize primes each, proper mu_n, never n=q-1):
  beta=4, n=16:  0.952 (p=65537),  0.912 (p=65617)   -> ~0.93
  beta=5, n=16:  0.951 (p=1048609), 0.966 (p=1048721) -> ~0.96
=> the gate ratio is beta-INVARIANT at n=16 (if anything slightly WEAKER at beta=5,
   not stronger), even though beta=5 is where the Sidon depth advantage is LARGEST.
   The depth->sup-norm conversion gains NOTHING from the deeper beta=5 Sidon depth.

ALSO (context): M_thin / M_generic-random ~ 1.07-1.14 (thin is WORSE than a generic,
NON-neg-closed random set of the same size). Thin only beats the NEG-CLOSED-random
control; that ~0.93-0.96 gap is the antipodal-structure penalty of the control, NOT a
2-power-subgroup bonus -- thin tracks ~0.92*sqrt(n log p), never a power below.

CONSTRAINT LEMMA (rule-4, tightening §7.2): the depth->sup-norm bootstrap failure is
beta-ROBUST. The Sidon depth advantage grows with both n and beta, but the sup-norm
gate ratio M_thin/M_neg-rand is flat (~0.93-0.96) across BOTH n and beta. A growing
depth is necessary-not-sufficient AND the deeper beta=5 regime (max depth) does NOT
improve the conversion. Any depth->sup-norm bootstrap must explain why MORE depth buys
NO sup-norm saving -- the conversion is the wall, and it does not soften where depth is
deepest.

HONEST SCOPE (rule-6): does NOT close/refute CORE. Sharpens the only-live thinness-
essential lead's wall by adding the beta-axis. n=16 two-prime per beta; n=32 beta=5
sup-sweep (p~3.3e7) is the heavy untested extension (left for a longer-budget run).
This builds on probe_407_supnorm_thinness_gate.py (the n-axis flatness at beta=4).
PROPER mu_n, prize-band p~n^beta, two primes per cell, never n=q-1.

Run: python3 probe_407_supnorm_gate_beta_invariance.py --n 16
(invokes the existing gate at beta=4 and beta=5 for direct comparison).
"""
import subprocess, sys, os, argparse, re

GATE = os.path.join(os.path.dirname(__file__), "probe_407_supnorm_thinness_gate.py")


def run_cell(n, beta, draws=6, timeout=110):
    out = subprocess.run(
        [sys.executable, "-u", GATE, "--n", str(n), "--beta", str(beta), "--draws", str(draws)],
        capture_output=True, text=True, timeout=timeout,
    ).stdout
    ratios = re.findall(r"ratio thin/neg-rand = ([\d.]+)", out)
    return [float(r) for r in ratios], out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--draws", type=int, default=6)
    a = ap.parse_args()
    print(f"SUP-NORM GATE beta-invariance test, n={a.n}")
    print("(M_thin / M_neg-closed-random; <1 => thin helps; flat across beta => depth wasted)")
    print("-" * 60)
    for beta in (4.0, 5.0):
        try:
            ratios, _ = run_cell(a.n, beta, a.draws)
            avg = sum(ratios) / len(ratios) if ratios else float("nan")
            print(f"  beta={beta}: ratios={ratios}  avg={avg:.3f}")
        except subprocess.TimeoutExpired:
            print(f"  beta={beta}: TIMEOUT (sup-sweep too heavy at this n; try smaller n)")
    print()
    print("VERDICT: if avg(beta=5) is NOT meaningfully below avg(beta=4), the deeper")
    print("Sidon depth at beta=5 buys NO sup-norm saving => depth->supnorm bootstrap")
    print("failure is beta-robust (tightens the §7.2 only-live thinness-essential wall).")


if __name__ == "__main__":
    main()
