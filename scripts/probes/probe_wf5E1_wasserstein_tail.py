#!/usr/bin/env python3
# wf-E1: Effective Wasserstein (Kowalski-Untrau 2505.22059) -> tail -> union-bound PRE-SCREEN.
#
# THE REDUCTION UNDER TEST.
# KU give an EFFECTIVE W_1 discrepancy for a trace-function family (indexed by a in F_q, size ~q):
#       W_1(mu_emp, mu_SatoTate)  <<  q^{-1/dim(K)}      (e.g. q^{-1/4} for SU_2 Kloosterman,
#       q^{-1/3} special). [Thm 4.4 + Thm 4.1/Borda, Thm 1.3(3,6,7).]
# mu_emp = (1/q) sum_a delta_{ S_a / sqrt(q) }  on the compact group K (or its trace image in C).
#
# We want:  max_b |S_b| <= C sqrt(n log m),  m = (p-1)/n = 2^128 fixed, n = 2^mu.
# Normalize x_b = S_b / sqrt(n). Want max_b |x_b| <= C sqrt(log m) ~ C sqrt(128 ln2) ~ 9.4 C.
#
# THE ROUTE: W_1 tail.  W_1(mu_emp, mu_target) <= D  means: for EVERY 1-Lipschitz u,
#       | (1/N) sum_b u(x_b)  -  E_target u |  <=  D.
# Take u_t(x) = max(0, |x|-t)  (1-Lipschitz).  Then
#       (1/N) sum_b max(0,|x_b|-t)  <=  E_target max(0,|x|-t)  +  D.
# The LHS >= (1/N) * #{b: |x_b| > t+1} * 1 ... actually >= (1/N)*(max-t) if max>t.
# So:   (max_b |x_b| - t)/N  <=  E_target u_t + D   =>   max_b|x_b| <= t + N*(E_target u_t + D).
# With N = q-1 ~ q and D = q^{-1/dim}, the term N*D ~ q^{1-1/dim} = q^{3/4} BLOWS UP.
# => W_1 -> single-outlier max is HOPELESS: one outlier moves W_1 by only 1/N, so W_1 <= D
#    permits an outlier of size up to ~ N*D.  This is the conservation wall (meta-thm).
#
# THE ONLY non-vacuous union route: a TAIL bound Pr_b[|x_b|>t] <= f(t) with f INDEPENDENT of N,
# then union over N=m frequencies needs f(t) <= 1/m i.e. need f(C sqrt(log m)) <= 1/m.
# Gaussian/semicircle tail f(t)=exp(-t^2/2) gives exactly the sqrt(log m) law (GOOD if we had it).
# But W_1 = D only yields, via Markov on u_t,  Pr[|x|>t+s] <= (E_target u_t + D)/s.
# The CONSTANT additive D does NOT decay in t, so it FLOORS the tail at ~D/s, NOT exp(-t^2/2).
# => union over m needs D/s <= 1/m i.e. D <= s/m ~ 1/m = 2^{-128}; but D = q^{-1/4} and
#    q = n*m = n*2^128, so q^{-1/4} = (n)^{-1/4} 2^{-32} >> 2^{-128}. FAILS by 2^96.
#
# THIS PROBE measures the empirical numbers behind every step so the wall is QUANTITATIVE,
# not hand-wavy.  We compute, for real thin 2-power subgroups:
#   (A) the W_1-style discrepancy of the empirical distribution of x_b=S_b/sqrt(n) vs the
#       limiting law (we test BOTH the complex-Gaussian/semicircle and the actual sample),
#   (B) the empirical tail Pr_b[|x_b|>t] vs the iid-Gaussian tail exp(-t^2/2)? (complex => exp(-t^2)),
#   (C) the implied union-bound max vs the true max,
#   (D) the q^{1-1/dim} blow-up factor at prize scale.

import numpy as np
from sympy import primitive_root, isprime
import math

def musub(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        G[i] = x
        x = (x * h) % p
    return G

def periods(n, p):
    """Return |S_b| for all b!=0, vectorized."""
    G = musub(n, p)
    b = np.arange(1, p, dtype=np.int64)            # (p-1,)
    # phase[b,y] = e_p(b*G[y]); sum over y. Build in blocks to save mem.
    out = np.empty(p - 1)
    w = 2j * np.pi / p
    BS = max(1, 2_000_000 // n)
    for s in range(0, p - 1, BS):
        bb = b[s:s + BS][:, None]                  # (B,1)
        ph = np.exp(w * ((bb * G[None, :]) % p))   # (B,n)
        out[s:s + BS] = np.abs(ph.sum(axis=1))
    return out

def w1_1d(samples, ref_samples):
    """W_1 on R between two empirical 1-D distributions = L1 of sorted-quantile diff."""
    a = np.sort(samples); bq = np.sort(ref_samples)
    # resample ref to len(a) via quantiles
    if len(a) != len(bq):
        q = (np.arange(len(a)) + 0.5) / len(a)
        bq = np.quantile(np.sort(ref_samples), q)
    return np.mean(np.abs(a - bq))

print("Pre-screen wf-E1: Wasserstein -> tail -> union-bound for thin 2-power subgroup")
print("=" * 100)

# regimes: n = 2^mu, p ~ n^beta (beta 2..3 computationally feasible; prize beta~4-5, n~2^30)
cases = []
for (mu, beta) in [(4, 2.2), (4, 2.6), (5, 2.0), (5, 2.4), (6, 2.0), (6, 2.3), (7, 2.0)]:
    n = 2 ** mu
    target = int(round(n ** beta))
    p = None
    for c in range(target - (target % n) + 1, target * 4, n):
        if c > 1 and isprime(c):
            p = c
            break
    if p:
        cases.append((n, p))

print(f"{'n':>4}{'p':>9}{'beta':>6}{'m=(p-1)/n':>11}{'max|x|':>9}{'sqrt(logm)':>11}"
      f"{'C=max/sqrtlogm':>15}{'tail@2.5':>10}{'GaussTail':>10}{'W1emp':>8}")
results = []
for (n, p) in cases:
    S = periods(n, p)
    x = S / math.sqrt(n)                 # normalized, b != 0
    N = p - 1
    m = (p - 1) // n
    mx = x.max()
    sq_logm = math.sqrt(math.log(m))
    C = mx / sq_logm
    beta = math.log(p) / math.log(n)
    # empirical tail at t=2.5 (in units of sqrt(n)); complex sum => |x|^2 ~ Exp => Pr[|x|>t]~exp(-t^2)
    t0 = 2.5
    tail_emp = np.mean(x > t0)
    tail_gauss = math.exp(-t0 * t0)      # complex Rayleigh-type
    # W_1 of empirical |x| vs Rayleigh(scale matched: E|x|^2=1 => Pr(|x|>t)=exp(-t^2))
    rng = np.random.default_rng(0)
    ref = np.sqrt(rng.exponential(1.0, size=len(x)))   # |x| with |x|^2 ~ Exp(1)
    w1 = w1_1d(x, ref)
    results.append((n, p, m, mx, C, w1, tail_emp, tail_gauss))
    print(f"{n:>4}{p:>9}{beta:>6.2f}{m:>11}{mx:>9.2f}{sq_logm:>11.2f}{C:>15.2f}"
          f"{tail_emp:>10.4f}{tail_gauss:>10.4f}{w1:>8.4f}")

print()
print("=" * 100)
print("PRIZE-SCALE BLOW-UP CHECK (the reduction wall):")
print("KU effective W_1 discrepancy D ~ q^{-1/dim(K)}. Best special case dim=2 (SU_2): D = q^{-1/2}.")
print("Generic Sato-Tate group for subgroup Gauss period: dim could be larger => weaker.")
for dim in [2, 3, 4]:
    # prize: n=2^30, m=2^128, q = n*m = 2^158
    logq = 158 * math.log(2)
    q = math.exp(logq)
    D = q ** (-1.0 / dim)
    m = 2 ** 128
    N = q  # ~ q-1 frequencies
    # single-outlier permitted size from W_1<=D:  max-t <= N*(E u_t + D); the N*D piece:
    blowup = N * D
    # union route needs additive floor D <= 1/m:
    print(f"  dim(K)={dim}: D=q^(-1/{dim})=2^{math.log2(D):+.1f} ;  "
          f"N*D=2^{math.log2(blowup):+.1f} (single-outlier slack) ;  "
          f"need D<=1/m=2^-128 ? {'YES' if D <= 1.0/m else 'NO, short by 2^%.0f'%(math.log2(D)-(-128))}")

print()
print("VERDICT: the ADDITIVE constant D in the W_1->tail Markov step does NOT decay in t,")
print("so it floors the tail and the union over m=2^128 frequencies cannot close unless")
print("D <= 1/m = 2^-128. KU give D = q^{-1/dim} with q=2^158 => D >= 2^-79 (dim=2). Short by 2^49+.")
print("This is the [P]-route analogue of the campaign's effective-Katz m/sqrt(q) ~ 2^48 wall.")
