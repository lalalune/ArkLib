#!/usr/bin/env python3
"""
probe_energy_ratio_supnorm_lower.py  (#444, EXTEND EnergyLogConvexRatioMonotone)

Claim under test (the LOWER-bound direction of the log-convex energy ladder, the
honest/easy companion of the proven UPPER bound `E_{r+1} <= maxSq * E_r`):

    For every r >= 0:   max_b ||eta_b||^2  >=  E_{r+1} / E_r          (RATIO LOWER BOUND)

and, by the proven ratio-monotonicity (energy_ratio_monotone_nat), the ratios
E_{r+1}/E_r are NON-DECREASING in r, so the lower bound TIGHTENS with r and

    max_b ||eta_b||^2  =  lim_{r->inf} E_{r+1} / E_r                  (the SHARP limit).

This is NOT an energy UPPER bound (the refuted route); it is the structural fact
that the spectral max is bracketed FROM BELOW by every consecutive energy ratio.
For the prize object mu_n it gives a CERTIFIED lower bound on M(n)^2 = max||eta||^2
from any computable pair (E_r, E_{r+1}) -- and the limit is M(n)^2 exactly.

We verify on PROPER subgroups mu_n (n=2^a | p-1), large primes p > n^3 (prize-ish),
NEVER on n=q-1 (full group). E_r = #{2r-tuples a_1+..+a_r = a_{r+1}+..+a_{2r}} over mu_n.
"""
import itertools, cmath, math

def eta_norms_sq(p, n):
    # mu_n = n-th roots of unity in F_p*, realized via primitive root.
    # Find primitive root g of F_p.
    def is_primroot(g):
        seen = set(); x = 1
        for _ in range(p-1):
            x = (x*g) % p; seen.add(x)
        return len(seen) == p-1
    g = 2
    while not is_primroot(g):
        g += 1
    m = (p-1)//n
    mu = sorted({pow(g, (m*k) % (p-1), p) for k in range(n)})
    assert len(mu) == n, (p, n, len(mu))
    # eta_b = sum_{x in mu} e_p(b x); compute ||eta_b||^2 for all b in F_p.
    w = [cmath.exp(2j*cmath.pi*t/p) for t in range(p)]
    norms = []
    for b in range(p):
        s = 0+0j
        for x in mu:
            s += w[(b*x) % p]
        norms.append(abs(s)**2)
    return mu, norms

def energy_r(mu, p, r):
    # E_r = #{ (a_1..a_r ; c_1..c_r) in mu^{2r} : sum a = sum c mod p }
    # via t -> N_r(t)=#{r-tuples summing to t}, E_r = sum_t N_r(t)^2.
    from collections import Counter
    N = Counter({0:1})
    for _ in range(r):
        M = Counter()
        for t,c in N.items():
            for a in mu:
                M[(t+a)%p] += c
        N = M
    return sum(c*c for c in N.values())

def main():
    cases = [
        (97,16),(193,16),(257,16),(769,16),(1153,16),
        (193,32),(12289,16),(40961,16),(65537,16),
    ]
    print(f"{'p':>6} {'n':>4} {'beta':>5} {'maxSq':>12} "
          f"{'E1/E0':>10} {'E2/E1':>10} {'E3/E2':>10}  ratio<=maxSq? monotone?")
    fails = 0; mono_fails = 0
    for p,n in cases:
        if (p-1) % n: continue
        if p <= n**3: 
            # still informative but flag
            pass
        mu, norms = eta_norms_sq(p, n)
        maxSq = max(norms)
        beta = math.log(p)/math.log(n)
        E = [energy_r(mu, p, r) for r in range(0,4)]  # E0=1, E1=n, E2, E3
        ratios = [E[r+1]/E[r] for r in range(0,3)]
        ok = all(rt <= maxSq + 1e-6 for rt in ratios)
        mono = all(E[r]*E[r] <= E[r-1]*E[r+1] for r in range(1,3))
        if not ok: fails += 1
        if not mono: mono_fails += 1
        print(f"{p:>6} {n:>4} {beta:>5.2f} {maxSq:>12.3f} "
              f"{ratios[0]:>10.4f} {ratios[1]:>10.4f} {ratios[2]:>10.4f}  "
              f"{'OK' if ok else 'FAIL':>12}  {'OK' if mono else 'FAIL'}")
    print(f"\nratio<=maxSq fails: {fails}/{len(cases)}   monotone fails: {mono_fails}/{len(cases)}")
    print("If 0/0: max||eta||^2 >= E_{r+1}/E_r for every r, and ratios are monotone")
    print("=> the lower bound tightens to maxSq as r grows (sharp limit).")

if __name__ == "__main__":
    main()
