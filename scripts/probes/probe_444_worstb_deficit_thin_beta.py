#!/usr/bin/env python3
"""
Door-IV Lane-1 probe (#444): worst-b deficit fraction ACROSS BETA at fixed small n,
to reach the THIN prize regime (beta=4..6) where the m=n^{beta-1} coset scan is still
tractable for small n.

We track at the worst frequency b* (max |eta_b|):
  rho2(b*) = |eta_b*|^2/n^2  (coherence^2)
  f(b*)    = 1-rho2          (total-pairwise-angular-deficit fraction; prize wants ->1)
vs the prize reference rho2 ~ log(p/n)/n (thin) and SOTA |eta|~n^0.989 -> rho2~n^-0.022.

KEY: holding n FIXED and increasing beta moves p up (q=n^beta) WITHOUT changing the
subgroup thinness exponent in the way n->infinity does; but it directly tests whether
the worst-b coherence at fixed n DECAYS as the field grows (more cosets to adversarially
pick from = larger sup). If rho2 GROWS with beta at fixed n, the sup is climbing toward
the wall; if it saturates, the deficit fraction is capped.  Empirical only, no claim.
"""
import math, numpy as np, sympy as sp
TAU = 2.0*math.pi

def prime_1_mod_n_near(n, target):
    k = max(1,(target-1+n-1)//n); p=k*n+1
    while not sp.isprime(p): k+=1; p=k*n+1
    return p

def worst(n, beta, mcap=4_000_000):
    p = prime_1_mod_n_near(n, n**beta)
    m = (p-1)//n
    if m > mcap:
        return None
    g = int(sp.primitive_root(p))
    mu = np.array([pow(g,(m)*t,p) for t in range(n)], dtype=np.int64)
    bestabs2 = -1.0; bestb = 1
    CH = 8192
    r = 1
    # iterate quotient reps g^j without storing all m: chunk by exponent
    for lo in range(0, m, CH):
        js = np.arange(lo, min(lo+CH, m))
        reps = np.array([pow(g,int(j),p) for j in js], dtype=np.int64)
        ang = (TAU/p)*np.outer(reps, mu)
        s = np.exp(1j*ang).sum(axis=1)
        a2 = s.real**2 + s.imag**2
        k = int(np.argmax(a2))
        if a2[k] > bestabs2:
            bestabs2 = float(a2[k]); bestb = int(reps[k])
    rho2 = bestabs2/(n*n)
    return dict(n=n, beta=beta, p=p, m=m, b=bestb, absEta=math.sqrt(bestabs2),
                rho2=rho2, f=1-rho2, prize_rho2=math.log(p/n)/n,
                sota_rho2=n**(-0.022))

if __name__=="__main__":
    print(f"{'n':>4} {'beta':>4} {'p':>14} {'m':>9} {'|eta|':>8} {'rho2':>8} "
          f"{'f':>7} {'prize_r2':>9} {'sota_r2':>8} {'r2/prize':>9} {'r2/sota':>8}")
    for n in (16, 32):
        for beta in (3,4,5,6):
            r = worst(n, beta)
            if r is None:
                print(f"{n:>4} {beta:>4}  (m too large, skipped)")
                continue
            print(f"{n:>4} {beta:>4} {r['p']:>14} {r['m']:>9} {r['absEta']:>8.3f} "
                  f"{r['rho2']:>8.4f} {r['f']:>7.4f} {r['prize_rho2']:>9.5f} "
                  f"{r['sota_rho2']:>8.5f} {r['rho2']/r['prize_rho2']:>9.3f} "
                  f"{r['rho2']/r['sota_rho2']:>8.4f}")
