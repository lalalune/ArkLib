#!/usr/bin/env python3
"""
#444 -- WHERE the cross-mass sits in the (s1,s2) sign-quadrants (refines twolevel_compose).

twolevel_compose found: p2/p1 = 1.000 (second halving FAILS) yet f_both = f1*f2 (sign COUNTS
independent). Reconcile: the MASS must concentrate on the both-+ quadrant. Measure the cross-mass
cm = ||eta_b||*||eta_{zeta b}|| split over the four sign quadrants of (s1, s2) where
s1 = Re eta_b * Re eta_{zeta b},  s2 = Re eta_{zeta^{-1} b} * Re eta_b.
If mass(++) ~ plusMass and mass(+-),(- -),(-+) ~ 0 on the heavy frequencies, the deep-descent
survivor (heavy) set is the both-+ set and the average halving CANNOT thin it. Refutation-with-
mechanism for the iterated-halving hope (MASS side), companion to survivor-honesty (COUNT side).
"""
import numpy as np

def find_prime(n, beta):
    target = int(n ** beta)
    p = target - (target % (2 * n)) + 1
    if p <= 2 * n:
        p += 2 * n
    while True:
        if p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)) and (p - 1) % (2 * n) == 0:
            return p
        p += 2 * n

def primitive_root(p):
    fac, m, d = [], p - 1, 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g

def run(n, beta):
    p = find_prime(n, beta)
    g = primitive_root(p)
    h = pow(g, (p - 1) // (2 * n), p)
    zeta, zinv = h, pow(h, p - 2, p)
    muN = np.array([pow(h, 2 * j, p) for j in range(n)], dtype=np.int64)
    seen = np.zeros(p, dtype=bool); reps = []
    for b in range(1, p):
        if seen[b]:
            continue
        seen[(b * muN) % p] = True; reps.append(b)
    reps = np.array(reps, dtype=np.int64)
    w = np.exp(2j * np.pi / p)
    def eta(bv):
        return (w ** ((np.outer(bv, muN)) % p)).sum(axis=1)
    eb, ezb, ezib = eta(reps), eta((zeta * reps) % p), eta((zinv * reps) % p)
    s1 = eb.real * ezb.real
    s2 = ezib.real * eb.real
    cm = np.abs(eb) * np.abs(ezb)
    tot = cm.sum()
    pp = cm[(s1 >= 0) & (s2 >= 0)].sum()
    pm = cm[(s1 >= 0) & (s2 < 0)].sum()
    mp = cm[(s1 < 0) & (s2 >= 0)].sum()
    mm = cm[(s1 < 0) & (s2 < 0)].sum()
    # also: avg |eta_b|^2 on both-+ heavy set vs overall, to show heaviness
    heavy_pp = float(np.mean((np.abs(eb)**2)[(s1>=0)&(s2>=0)]))
    heavy_all = float(np.mean(np.abs(eb)**2))
    return dict(n=n, p=p,
                pp=pp/tot, pm=pm/tot, mp=mp/tot, mm=mm/tot,
                heavy_ratio=heavy_pp/heavy_all)

if __name__ == "__main__":
    print("=== cross-mass localization over (s1,s2) quadrants (frac of total) ===")
    print(f"{'n':>4} {'p':>9} {'mass++':>7} {'mass+-':>7} {'mass-+':>7} {'mass--':>7} {'heavy++/all':>11}")
    for a in range(3, 7):
        n = 2 ** a
        r = run(n, 4)
        print(f"{r['n']:>4} {r['p']:>9} {r['pp']:>7.3f} {r['pm']:>7.3f} {r['mp']:>7.3f} "
              f"{r['mm']:>7.3f} {r['heavy_ratio']:>11.3f}")
    print()
    print("READ: mass++ ~ 0.5 (=plusMass/tot) & mass-- ~0.5, mass+-,-+ ~ 0 => the heavy cross-mass")
    print("      lives on the SIGN-COHERENT quadrants (++ and --), NOT the mixed ones. heavy++/all>1")
    print("      => both-+ frequencies are HEAVIER than average => avg halving can't thin the heavy set.")
