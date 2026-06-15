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
    # n=32 k=4 (rho=1/8) CONFIRMED crossing (p=100000193 >> n^3=32768): r=23 GOOD (worst I=2,
    # binder (20,4)=x^k), r=24 BAD (worst I>=97, binder (18,4)=x^k) -> delta* = 23/32 = 0.71875.
    # NOTE: n=32 worst over far pencils used a binder-region a-scan (a in 12..23, b in {4,5,6}),
    # justified by the n=16 binder = x^k low-exp direction; the full a-sweep is compute-bound.
    (32,4): (23/32, "r=24 I>=97 binder (18,4)=x^k; r=23 good I=2 binder (20,4); binder-region scan"),
}

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
    for (n,k) in [(16,2),(32,4),(16,4)]:
        rho=k/n; cap=1-rho
        ds,_=DELTASTAR[(n,k)]
        offset = round(n*(cap-ds))
        print(f"  n={n} rho={rho}: w*-k = n*(cap-delta*) = {offset}   log2(n) = {math.log2(n):.0f}   "
              f"{'== log2(n)' if offset==round(math.log2(n)) else '!= log2(n)  <== CANDIDATE FAILS'}")
    print("  => w*-k = log2(n) HOLDS at rho=1/8 for BOTH n=16 (4) and n=32 (5), but FAILS at")
    print("     rho=1/4 n=16 (offset 3, not log2(16)=4). The crossing offset is RATE-DEPENDENT,")
    print("     so 'log2(n)/n' is NOT a clean rho-uniform closed form (refuted by the second rate).")
    print("\n" + "="*72)
    print("VERDICT: I_0(delta) has NO clean rho-uniform closed form in the window interior.")
    print("  - Below Johnson: I_0 ~ O(1) (trivial). Past the crossing: SUPER-POLYNOMIAL growth")
    print("    (k=4: 9->89->3696, ratios ~10x,~42x), -> C(n,r) only at the extreme boundary.")
    print("  - delta* numerically coincides with DIFFERENT closed forms per rate (discretization")
    print("    artifact: delta* is a rung r/n). Crossing offset w*-k: 4 (rho1/8,n16), 5 (rho1/8,n32),")
    print("    3 (rho1/4,n16) -> log2(n) only at rho=1/8; rate-dependent constant, no clean form.")
    print("  - Cross-validates the committed Mann/Lam-Leung refutation (DISPROOF_LOG 2026-06-14 P4):")
    print("    free-coefficient interpolation incidence, NOT antipodal/Mann-closeable in the window.")
    print("  => the char-0 worst-case incidence is the SAME open BGK/counting object; it does NOT")
    print("     reduce to a proven Mann/Lam-Leung closed form. See DISPROOF_LOG for the full entry.")
