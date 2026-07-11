#!/usr/bin/env python3
"""
wf-D2 (#444) SYNTHESIS: closed form for the binding far-line incidence and delta* vs the floor.

EXACT DATA (this lane, vectorized, p-independent; cross-checked vs in-tree
probe_farline_incidence_exact and the GPU H100 oracle on #444):

  far-line incidence at over-det level c = s-k (worst monomial direction b=k), budget = n:
    n=8  (k=2): s-k=4 -> 1 ; s-k=3 -> 8 ; s-k=2 -> 9 ; s-k=1 -> 40
    n=16 (k=4): s-k=4 -> 9 ; s-k=3 -> 9 ; s-k=2 -> 89 ; s-k=1 -> 3696
    n=24 (k=6): s-k=2 -> 1153 ; (binding levels below)

  delta* = (n - s*)/n, s* = smallest witness size with worst far incidence <= budget n.

  EXACT s*/delta* (n<=16 this lane; n=16..38 GPU H100, prize prime p~n^4, p-INDEPENDENT):
    n=8 : s*=5  delta*=0.3750   (small-n boundary; under-det reaches s=5)
    n=16: s*=7  delta*=0.5625 = 1/2+1/16   [I(16)=89 at s=6, the established data point]
    n=20: s*=9  delta*=0.5500 = 1/2+1/20
    n=24: s*=11 delta*=0.5417 = 1/2+1/24
    n=28: s*=13 delta*=0.5357 = 1/2+1/28
    n=32: s*=13 delta*=0.5938  (JUMP: s* did NOT reach 15=2k-1)
    n=34: s*=13 delta*=0.6176  (GPU: deep configs near limit)
    n=38: s*=13 delta*=0.6579  (GPU: n>=36 deep-binding TIMED OUT -> s* may be a compute ceiling)
"""
import math

REGIME_A = [(16,4,7,0.5625),(20,5,9,0.5500),(24,6,11,0.5417),(28,7,13,0.5357)]
REGIME_B = [(32,8,13,0.5938),(34,9,13,0.6176),(38,10,13,0.6579)]

def main():
    print("="*70)
    print("CLOSED FORM (regime A, n=16..28, ALL EXACT 4/4):")
    print("   s* = 2k-1 = n/2 - 1   (binding over-det level c* = k-1 = n/4-1)")
    print("   delta* = (n - s*)/n = (n/2 + 1)/n = 1/2 + 1/n")
    print("   = JOHNSON(rho=1/4)=1-sqrt(rho)=1/2  +  exactly one rung 1/n.")
    print("="*70)
    for (n,k,ss,ds) in REGIME_A:
        pred=0.5+1.0/n
        print(f"   n={n} k={k}: s*={ss}=2k-1? {ss==2*k-1}  delta*={ds:.4f}  1/2+1/n={pred:.4f}  {'OK' if abs(ds-pred)<1e-3 else 'MISS'}")
    print()
    print("ASYMPTOTIC: as n->inf, delta*(regime A) -> 1/2 = Johnson radius (1-sqrt(rho)).")
    print("            The prize FLOOR is 1-rho-Theta(1/log n) = 3/4 - Theta(1/log n) for rho=1/4.")
    print("            => regime-A delta* CONVERGES TO JOHNSON 1/2, a CONSTANT GAP 1/4 BELOW the floor.")
    print("            The window interior (1-sqrt(rho), 1-rho) = (1/2, 3/4) is NOT reached by the")
    print("            far-line incidence threshold in regime A: delta* sits at the LEFT endpoint +1/n.")
    print()
    print("REGIME B (n>=32): delta* JUMPS UP and climbs toward the floor:")
    for (n,k,ss,ds) in REGIME_B:
        c=(0.75-ds)*math.log2(n)
        print(f"   n={n} k={k}: s*={ss} (NOT 2k-1={2*k-1})  delta*={ds:.4f}  implied (3/4-delta*)*log2 n = {c:.3f}")
    print()
    print("HONEST CAVEAT: s* PINS at exactly 13 across n=32,34,38 while it strictly increased")
    print("   7,9,11,13 in regime A. GPU oracle flagged n>=36 deep-binding configs TIMED OUT.")
    print("   A pinned s*=13 with climbing delta* is the SIGNATURE of a search ceiling, NOT a law.")
    print("   If true s* continued =2k-1, delta* would stay 1/2+1/n -> 1/2 (Johnson), away from floor.")
    print("   The genuine open question: is n=32 s*=13 a REAL deviation (delta* climbing to floor)")
    print("   or the first compute-limited config?  n=32 was reported within H100 reach (s=14 checked).")
    print()
    print("VERDICT: closed form delta* = 1/2 + 1/n is PROVEN-EXACT for n=16..28 (= Johnson + 1/n).")
    print("   It does NOT match the floor 1-rho-Theta(1/log n); it matches the JOHNSON endpoint.")
    print("   => the far-line incidence threshold is a computable combinatorial quantity that pins")
    print("   delta* to JOHNSON+1/n in regime A, i.e. it does NOT certify the prize window interior.")
    print("   Regime-B climb is unconfirmed (s*-pin = likely compute ceiling).")

if __name__ == '__main__':
    main()
