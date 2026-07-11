#!/usr/bin/env python3
"""
Door-IV Lane-1 probe (#444): the TOTAL PAIRWISE ANGULAR DEFICIT LAW at the worst frequency.

The angular-deficit theory (_DoorIVTwoPieceAngularDeficit, sweeps 1-8 by sol-1781948404)
proved EXACTLY:
    |Sum z_i|^2 = (Sum |z_i|)^2 - 2 * D,   D = Sum_{i<j} ( |z_i||z_j| - Re<z_i,z_j> ) >= 0
and the prize ceiling  |Sum z|^2 <= T   <=>   D >= (L1^2 - T)/2.

The OPEN burden (its own handoff): does the WORST-b coset sum's total pairwise angular
deficit D(b) actually reach the prize-required level, or saturate strictly below it?

Concrete instantiation here: pieces = the m-fold coset decomposition of
    eta_b = Sum_{x in mu_n} e_p(b*x),  mu_n the 2-power subgroup,
into its n single-element "pieces" z_x = e_p(b*x) (so L1 = n exactly, each |z_x|=1).
Then  D(b) = Sum_{x<y} (1 - cos(2pi b (x-y)/p)) = C(n,2) - (1/2)(|eta_b|^2 - n).
=> |eta_b|^2 = n^2 - 2 D(b),  and the prize M(n) <= C*sqrt(n log(p/n)) is EXACTLY
    D(b) >= (n^2 - C^2 n log(p/n)) / 2  =  n^2/2 (1 - o(1))   at the WORST b.

So the prize, in angular-deficit language, asks: is the worst-b deficit FRACTION
    f(b) = D(b) / (n^2/2) = 1 - |eta_b|^2/n^2
forced to 1 - o(1)?  Equivalently is min_b |eta_b|^2/n^2 -> 0?  (max_b case is the wall.)

We measure, at the WORST (max |eta_b|) frequency b*:
    rho2(b*) = |eta_b*|^2 / n^2      (coherence^2; prize needs -> 0 i.e. log/n)
    f(b*)    = 1 - rho2(b*)          (deficit fraction; prize needs -> 1)
and compare f(b*) to the prize target  1 - C^2 log(p/n)/n.
This is NON-MOMENT (it's the exact geometric identity), NON-completion, and probes the
ARITHMETIC of {b*x} directly.  Empirical only; no claim.
"""
import math, numpy as np, sympy as sp

TAU = 2.0*math.pi

def prime_1_mod_n_near(n, target):
    k = max(1, (target-1+n-1)//n); p = k*n+1
    while not sp.isprime(p): k += 1; p = k*n+1
    return p

def worst_b(n, beta):
    p = prime_1_mod_n_near(n, n**beta)
    m = (p-1)//n
    g = int(sp.primitive_root(p))
    mu = np.array([pow(g, m*t, p) for t in range(n)], dtype=np.int64)  # subgroup mu_n
    reps = np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)  # coset reps
    # eta_b is constant on b's mu_n-coset; scan the m quotient reps
    best = -1.0; bestj = 0; bestb = 1
    # batch
    CH = 4096
    bestabs2 = -1.0
    for lo in range(0, m, CH):
        rr = reps[lo:lo+CH]
        # phases: for each rep r, sum over x in mu_n of e_p(r*x)
        ang = (TAU/p) * np.outer(rr, mu)        # (chunk, n)
        s = np.exp(1j*ang).sum(axis=1)          # (chunk,)
        a2 = (s.real**2 + s.imag**2)
        k = int(np.argmax(a2))
        if a2[k] > bestabs2:
            bestabs2 = float(a2[k]); bestb = int(rr[k]); bestj = lo+k
    rho2 = bestabs2 / (n*n)
    f = 1.0 - rho2
    logfac = math.log(p/n)
    # prize target deficit fraction (with C=1 normalization reference)
    prize_f_target = 1.0 - logfac/n
    return dict(n=n, beta=beta, p=p, m=m, worst_b=bestb,
                absEta=math.sqrt(bestabs2), rho2=rho2, deficit_frac=f,
                logfac=logfac, prize_f_target=prize_f_target,
                # SOTA n^0.989 reference: |eta| ~ n^0.989 => rho2 ~ n^{-0.022}
                sota_rho2=n**(-0.022),
                # prize reference: |eta| ~ sqrt(n logfac) => rho2 = logfac/n
                prize_rho2=logfac/n)

def tractable_beta(n, mcap=2_000_000):
    # pick the largest integer beta>=3 s.t. m=(p-1)/n ~ n^{beta-1} <= mcap
    b = 3
    while (n**(b))/n <= mcap:
        b += 1
    return max(3, b-1)

if __name__ == "__main__":
    print(f"{'n':>5} {'beta':>4} {'p':>13} {'m':>9} {'worst_b':>9} {'|eta|':>9} {'rho2':>9} "
          f"{'deficit_f':>10} {'prize_rho2':>11} {'sota_rho2':>10} {'rho2/sota':>9}")
    for a in range(4, 9):   # n = 16..256, FIXED beta=3 (clean law, m=n^2 tractable)
        n = 2**a
        beta = 3
        r = worst_b(n, beta)
        print(f"{r['n']:>5} {beta:>4} {r['p']:>13} {r['m']:>9} {r['worst_b']:>9} {r['absEta']:>9.3f} "
              f"{r['rho2']:>9.4f} {r['deficit_frac']:>10.4f} {r['prize_rho2']:>11.5f} "
              f"{r['sota_rho2']:>10.5f} {r['rho2']/r['sota_rho2']:>9.3f}")
