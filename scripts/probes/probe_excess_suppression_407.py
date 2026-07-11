#!/usr/bin/env python3
"""
#407 — THE DECISIVE SCALING CHECK: is the F_q-EXCESS of the vanishing-power-sum variety SUPPRESSED
at the binding window-edge t₀ in the PRIZE REGIME (large security gap λ)?

The variety #{S: e_1..e_{t-1}=0 in F_q} = (char-0 coset-union members) + (F_q-random excess).
The excess ≈ C(n, k+t) / q^{t-1}  (random heuristic; this IS the F_q-specific 'wall' part).
The char-0 members (Lam-Leung μ_{2^j}-coset unions) are forced, q-independent, and PROVABLE.

CLAIM: in the prize regime (ε*=2^{-λ}, λ=128, q ≈ n·2^λ), at the binding window-edge t₀ (where the
char-0 count crosses the budget qε*=n), the excess C(n,k+t₀)/q^{t₀-1} ≪ 1, so #bad γ ≈ char-0 only
⟹ δ* governed by the PROVABLE char-0 count, NOT the F_q wall. The wall (large excess) lives only at
small t (near capacity), ABOVE δ*, where it does not bind.

This script computes, for prize params, the window-edge t₀ and the suppression ratio
log₂(excess) = log₂ C(n,k+t₀) − (t₀−1) log₂ q, confirming it is ≪ 0 (suppressed) in the prize
regime and tracking how it depends on λ (it must FAIL for λ≈0, HOLD for λ=128).
"""
import math

def log2binom(n, k):
    if k<0 or k>n: return float('-inf')
    if k==0 or k==n: return 0.0
    # Stirling / lgamma
    from math import lgamma, log
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/log(2)

def Hb(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

def window_edge_t(n, rho, log2_q, log2_budget):
    """t₀ ≈ the gap where the char-0 coset-union count ~ budget.  The char-0 (ladder/N_fib)
    crossover is prizeDeltaStar: η₀ = H(ρ)/log2(budget), t₀ = η₀·n."""
    eta0 = Hb(rho)/log2_budget
    return eta0*n

print("="*94)
print("EXCESS SUPPRESSION at the binding window-edge t₀, across the PRIZE REGIME (q=n·2^λ, qε*=n)")
print("  excess ≈ C(n,k+t₀)/q^{t₀-1};  log₂(excess) ≪ 0  ⟹  F_q wall SUPPRESSED ⟹ δ* = char-0 (provable)")
print("="*94)
print(f"{'rho':>6} {'μ(n=2^μ)':>9} {'λ':>4} | {'log2 q':>7} {'t₀':>10} {'a/n':>6} | "
      f"{'log2 C(n,a)':>11} {'(t₀-1)log2q':>11} {'log2(excess)':>12} {'suppressed?':>11}")

prize_rates=[(0.5,"1/2"),(0.25,"1/4"),(0.125,"1/8"),(0.0625,"1/16")]
for rho,rl in prize_rates:
    for mu in (20,30,40):
        n=2**mu
        for lam in (128,):   # prize security parameter
            log2_q = mu + lam          # q = n·2^λ = 2^{μ+λ}
            log2_budget = math.log2(n) # qε* = n  ⟹ log2 budget = μ
            t0 = window_edge_t(n, rho, log2_q, log2_budget)
            k = rho*n
            a = k + t0
            lcb = log2binom(n, int(round(a)))
            qpow = (t0-1)*log2_q
            log2_excess = lcb - qpow
            supp = log2_excess < 0
            print(f"{rl:>6} {mu:>9} {lam:>4} | {log2_q:>7.0f} {t0:>10.1f} {a/n:>6.3f} | "
                  f"{lcb:>11.1f} {qpow:>11.1f} {log2_excess:>12.1f} {str(supp):>11}")
    print()

print("="*94)
print("CONTROL: vary λ at fixed (ρ=1/4, μ=40) — suppression must FAIL at small λ, HOLD at λ=128")
print("="*94)
print(f"{'λ':>5} | {'log2 q':>7} {'t₀':>10} | {'log2(excess)':>12} {'suppressed?':>11}")
rho=0.25; mu=40; n=2**mu
for lam in (0, 8, 16, 32, 64, 96, 128, 200):
    log2_q = mu + lam
    log2_budget = mu  # qε* = n
    t0 = window_edge_t(n, rho, log2_q, log2_budget)
    a = rho*n + t0
    log2_excess = log2binom(n, int(round(a))) - (t0-1)*log2_q
    print(f"{lam:>5} | {log2_q:>7.0f} {t0:>10.1f} | {log2_excess:>12.1f} {str(log2_excess<0):>11}")
print()
print("If log2(excess)≪0 at λ=128 across all rates/sizes: the F_q wall is SUPPRESSED at the binding")
print("radius ⟹ δ* = prizeDeltaStar reduces to the CHAR-0 Lam-Leung coset count (provable) +")
print("a NEGLIGIBLE excess — a path around the 25-yr F_q character-sum wall, SPECIFIC to large λ.")
