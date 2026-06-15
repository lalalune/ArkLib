#!/usr/bin/env python3
"""
P1-char0-closedform ANALYSIS [#407]: closed-form test for the char-0 worst-case far-line
incidence I_0(delta) at constant rate. Consolidates the EXACT p-INDEPENDENT data computed by
probe_p1_char0.py (deltastar_fast / deltastar_targeted), and tests it against candidate closed
forms (1-rho-c/log2 n, 1-rho-H/(beta log n), 1-rho-1/n, antipodal/Mann counts).

All I_0 values below are EXACT (no sqrt-loss), p-INDEPENDENT in the char-0-faithful regime
(p >> n^3; verified identical across multiple primes by probe_p1_char0.py), and were validated:
  - efficient (k+1)-subset method == brute agreement-set enumerator (n=8 exhaustive, b!=n/2),
  - numpy histogram == pure-Python histogram (n=16, all directions),
  - numpy AgreeEngine == pure-Python agreement (n=16, 200 survivors),
  - full fast pipeline reproduces the independent probe_farline_incidence_exact result
    (n=16 k=4: r=10 -> I=89 first-bad, binder (a=10,b=4=x^k), delta*=9/16).
"""
import math

# EXACT, p-INDEPENDENT data (from probe_p1_char0.py deltastar_fast):
DATA = {
    # (n,k): {r: I_0(r)}  far-line worst-case incidence (b != n/2 excluded)
    (16, 2): {3:1,4:1,5:1,6:1,7:1,8:2,9:5,10:5,11:17,12:97,13:464},
    (16, 4): {5:1,6:1,7:1,8:9,9:9,10:89,11:3696},
}
# delta* crossing (last good rung / n) and binder
DELTASTAR = {
    (16,2): (10/16, "r=11 I=17 binder (9,4)"),
    (16,4): (9/16,  "r=10 I=89 binder (10,4)=x^k"),
}
# n=32 PARTIAL (full worst-case far-pencil scan is compute-bound ~hours; these are CONFIRMED
# data points from full-direction-scans that ran before timeout, p=100000193 >> n^3=32768):
#   r=24 (delta=0.750): OVER-BUDGET worst I>=97 at pencil (a=18, b=4=x^k)  => r=24 is BAD.
#   r=19..25, low-exp dirs (a=31,b=4),(a=28,b=4): I=0 (well below the crossing).
#   Crossing is at r<=24; consistent with the parallel-agent rho=1/8 candidate (r*=23 => w*-k=5),
#   but the closed-form REFUTATION rests on the rho-DEPENDENT crossing offset (4 at rho=1/8 vs
#   3 at rho=1/4), independent of the n=32 point.
N32_PARTIAL = {(32,4): {24: ">=97 (BAD, binder a=18 b=4=x^k)", "low-exp dirs r19-25": 0}}

def closed_forms(n, k):
    rho = k/n
    H = -rho*math.log2(rho) - (1-rho)*math.log2(1-rho)
    return {
        "Johnson 1-sqrt(rho)":   1 - rho**0.5,
        "capacity 1-rho":        1 - rho,
        "1-rho-1/log2(n)":       1 - rho - 1/math.log2(n),
        "1-rho-H(rho)/log2(n)":  1 - rho - H/math.log2(n),
        "1-rho-H/(2 log2 n)":    1 - rho - H/(2*math.log2(n)),
        "1-rho-1/n":             1 - rho - 1/n,
        "Johnson + 1/n":         1 - rho**0.5 + 1/n,
    }

if __name__ == '__main__':
    print("="*72)
    print("CHAR-0 WORST-CASE FAR-LINE INCIDENCE I_0(delta) AT CONSTANT RATE")
    print("="*72)
    for (n,k) in [(16,2),(16,4)]:
        rho = k/n
        print(f"\n--- n={n} k={k} rho={rho} (budget n={n}) ---")
        print(f"  {'r':>3} {'delta':>7} {'I_0':>7}  growth-ratio  C(n,r)")
        prev=None
        for r in sorted(DATA[(n,k)]):
            I=DATA[(n,k)][r]
            gr = f"{I/prev:6.2f}x" if prev else "   -"
            print(f"  {r:>3} {r/n:7.4f} {I:>7}  {gr:>8}    {math.comb(n,r)}")
            prev=I
        ds,binder=DELTASTAR[(n,k)]
        print(f"  delta* = {ds:.4f}  ({binder})")
        print(f"  closed-form candidates (delta* - cf):")
        for name,v in closed_forms(n,k).items():
            mark = "  <== EXACT MATCH" if abs(ds-v)<1e-9 else ""
            print(f"    {name:24s} = {v:.4f}   (Delta = {ds-v:+.4f}){mark}")
    print("\n" + "="*72)
    print("CROSSING-OFFSET TEST: n*(cap-delta*) = (n-k) - r*_lastgood = (w*-k)")
    print("="*72)
    print("  candidate (parallel agent, probe_char0_deltastar_pin_constrate): w*-k = log2(n).")
    for (n,k) in [(16,2),(16,4)]:
        rho=k/n; cap=1-rho
        ds,_=DELTASTAR[(n,k)]
        offset = round(n*(cap-ds))
        print(f"  n={n} rho={rho}: w*-k = n*(cap-delta*) = {offset}   log2(n) = {math.log2(n):.0f}   "
              f"{'== log2(n)' if offset==round(math.log2(n)) else '!= log2(n)  <== CANDIDATE FAILS'}")
    print("  => offset is 4 at rho=1/8 but 3 at rho=1/4 (both n=16): RATE-DEPENDENT, not a clean")
    print("     rho-uniform closed form. The 'log2(n)' match at rho=1/8 is a coincidence.")
    print("\n" + "="*72)
    print("VERDICT: I_0(delta) has NO clean rho-uniform closed form in the window interior.")
    print("  - Below Johnson: I_0 ~ O(1) (trivial). Past the crossing: SUPER-POLYNOMIAL growth")
    print("    (k=4: 9->89->3696, ratios ~10x,~42x), -> C(n,r) only at the extreme boundary.")
    print("  - delta* numerically coincides with DIFFERENT closed forms per rate (discretization")
    print("    artifact: delta* is a rung r/n). The crossing-offset w*-k is rate-dependent (4 vs 3).")
    print("  - Cross-validates the committed Mann/Lam-Leung refutation (DISPROOF_LOG 2026-06-14 P4):")
    print("    free-coefficient interpolation incidence, NOT antipodal/Mann-closeable in the window.")
    print("  => the char-0 worst-case incidence is the SAME open BGK/counting object; it does NOT")
    print("     reduce to a proven Mann/Lam-Leung closed form. See DISPROOF_LOG for the full entry.")
