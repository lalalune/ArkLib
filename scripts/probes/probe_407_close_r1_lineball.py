#!/usr/bin/env python3
"""
probe_407_close_r1_lineball.py  (#407 R1, FAST line-ball / coefficient-space form)

KEY STRUCTURAL FACT (verified, /tmp/verify_syndrome_dft.py): for U(X)=sum_d u_d X^d
(deg<n) evaluated on mu_n, the RS[mu_n,k] syndrome is exactly the HIGH-COEFFICIENT
vector  s(U) = (u_k, u_{k+1}, ..., u_{n-1})  (up to the scalar n).  Hence:
   #bad(U0,U1) = #{ gamma : the high-coeff line s0 + gamma*s1 is the syndrome of a
                            word within distance w=n-a of the code }.
The bad set depends ONLY on (s0,s1) in F_q^{n-k}; lower-degree (<k) coeffs are FREE.

R1: among lines with s1 top-support index b*, s0 top-support index a*, the MONOMIAL
line (s0=e_{a*}, s1=e_{b*}) maximizes #bad (incidence with the syndrome ball S_w).

FAST exact oracle 'within_w(vec)':  vec is within distance w of RS[mu_n,k] iff some
deg<k poly agrees with vec on >= a=n-w points.  We enumerate k-subsets ONCE
(precomputed Lagrange), dedup interpolants by their evaluation tuple, and early-exit.
For k=2 this is O(n^2) pairs -> very fast; we run k=2 (exhaustive over pencils) AND k=4.

Adversarial: full/near-full sweep over combination pencils of the SAME leading degrees.
Any strict excess REFUTES R1.
"""
import itertools, random, sys
from itertools import combinations

def gen(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p; seen.add(x)
        if len(seen) == p - 1:
            return g
    raise RuntimeError

def rou(p, n):
    g = gen(p); w = pow(g, (p - 1) // n, p)
    return [pow(w, i, p) for i in range(n)]

def inv(a, p): return pow(a, p - 2, p)

def precompute_lagrange(mu, k, p):
    n = len(mu); out = []
    for T in combinations(range(n), k):
        xs = [mu[i] for i in T]; lag = []; ok = True
        for jj in range(n):
            row = []
            for t in range(k):
                num = 1; den = 1
                for u in range(k):
                    if u != t:
                        num = num * (mu[jj] - xs[u]) % p
                        den = den * (xs[t] - xs[u]) % p
                if den == 0: ok = False; break
                row.append(num * inv(den, p) % p)
            if not ok: break
            lag.append(row)
        if ok: out.append((T, lag))
    return out

def within_w(vec, mu, k, p, a, combos_k):
    n = len(mu)
    for (T, lag) in combos_k:
        ys = [vec[i] for i in T]; ag = 0
        for jj in range(n):
            v = 0; Lj = lag[jj]
            for t in range(k):
                v += ys[t] * Lj[t]
            if v % p == vec[jj]:
                ag += 1
                if ag >= a:  # cannot early-exit fully since remaining could still help, but >=a is enough
                    return True
    return False

def badset_from_coeffs(s0, s1, mu, k, p, a, combos_k):
    """s0,s1 are full coeff dicts deg->coef (degrees in [k,n-1]); lower <k absorbed/free.
    Build eval vector of (s0 + gamma s1) as a polynomial (low coeffs 0) and test within_w."""
    n = len(mu); bad = []
    # precompute per-point base values: B0[i]=sum s0[d] mu_i^d, B1[i]=sum s1[d] mu_i^d
    B0 = [sum(c * pow(mu[i], d, p) for d, c in s0.items()) % p for i in range(n)]
    B1 = [sum(c * pow(mu[i], d, p) for d, c in s1.items()) % p for i in range(n)]
    for gamma in range(p):
        vec = [(B0[i] + gamma * B1[i]) % p for i in range(n)]
        if within_w(vec, mu, k, p, a, combos_k):
            bad.append(gamma)
    return bad

def main():
    random.seed(7)
    for (n, k, primes, deg_pairs, radii, full_sweep) in [
        # k=2: RS lines. Johnson = sqrt(2n). beyond-Johnson a small. EXHAUSTIVE pencil sweep.
        (16, 2, [97, 113, 193], [(9, 5), (7, 3), (11, 5), (13, 9)], [6, 7], True),
        # k=4: original Kambire test case
        (16, 4, [97, 193], [(9, 5), (7, 5), (11, 9)], [9, 10], False),
    ]:
        for p in primes:
            if (p - 1) % n: continue
            mu = rou(p, n)
            combos_k = precompute_lagrange(mu, k, p)
            print(f"\n=== p={p} RS[mu_{n},k={k}] Johnson~{(n*k)**.5:.2f} ({len(combos_k)} k-subsets) ===", flush=True)
            for (astar, bstar) in deg_pairs:
                for a in radii:
                    bc_mono = len(badset_from_coeffs({astar: 1}, {bstar: 1}, mu, k, p, a, combos_k))
                    if bc_mono == 0: continue
                    highdegs = [d for d in range(k, n) if d not in (astar, bstar)]
                    excess = []; ties = 0; trials = 0
                    cand = []
                    if full_sweep:
                        # exhaustive over ONE extra high coeff on each side (all field values)
                        for d in highdegs:
                            for c in range(1, p):
                                cand.append(({astar: 1}, {bstar: 1, d: c}))
                                cand.append(({astar: 1, d: c}, {bstar: 1}))
                        # plus random both-perturbed (2 extra terms each)
                        for _ in range(200):
                            u0 = {astar: 1}; u1 = {bstar: 1}
                            for d in random.sample(highdegs, k=min(3, len(highdegs))):
                                (u0 if random.random() < .5 else u1)[d] = random.randrange(1, p)
                            cand.append((u0, u1))
                    else:
                        step = max(1, p // 12)
                        for d in highdegs:
                            for c in range(1, p, step):
                                cand.append(({astar: 1}, {bstar: 1, d: c}))
                                cand.append(({astar: 1, d: c}, {bstar: 1}))
                        for _ in range(40):
                            u0 = {astar: 1}; u1 = {bstar: 1}
                            for d in random.sample(highdegs, k=min(2, len(highdegs))):
                                (u0 if random.random() < .5 else u1)[d] = random.randrange(1, p)
                            cand.append((u0, u1))
                    for (u0c, u1c) in cand:
                        trials += 1
                        bc = len(badset_from_coeffs(u0c, u1c, mu, k, p, a, combos_k))
                        if bc > bc_mono: excess.append((bc, u0c, u1c))
                        elif bc == bc_mono: ties += 1
                    tag = "R1-OK" if not excess else "*** R1 REFUTED ***"
                    print(f"  (a*,b*)=({astar},{bstar}) a={a}: mono={bc_mono} trials={trials} "
                          f"ties={ties} excess={len(excess)} {tag}", flush=True)
                    for bc, u0c, u1c in sorted(excess, key=lambda t: -t[0])[:5]:
                        print(f"      EXCESS bc={bc}: U0={u0c} U1={u1c}", flush=True)

if __name__ == "__main__":
    main()
