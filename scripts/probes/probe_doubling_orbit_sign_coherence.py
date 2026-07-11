#!/usr/bin/env python3
"""
#444 -- WHY mass(+-)=mass(-+)=0: orbit-sign-coherence of the heavy frequencies.

twolevel_massloc showed the cross-mass lives ONLY on the sign-coherent quadrants (++ and --).
s1(b) = Re eta_b * Re eta_{zeta b},  s2(b) = Re eta_{zeta^{-1} b} * Re eta_b.
Note s2(b) = Re eta_{zeta^{-1} b} * Re eta_b = s1(zeta^{-1} b).  So mixed-sign means
sign(Re eta_b * Re eta_{zeta b}) != sign(Re eta_{zeta^{-1}b} * Re eta_b), i.e. the product of the
three consecutive orbit reals Re eta_{zeta^{-1}b}, Re eta_b, Re eta_{zeta b} changes the adjacent
pair-sign. Test the DIRECT mechanism: is Re eta_b ITSELF sign-constant along the zeta-orbit on the
HEAVY frequencies?  i.e. does sign(Re eta_{zeta^j b}) stay fixed as j runs the orbit, for b with
large ||eta_b||?  If yes on the heavy set => the cross-signs are all + (or the alternation is
forced) => coherence is an orbit-sign-rigidity fact, the real obstruction to iterated halving.
"""
import numpy as np

def find_prime(n, beta):
    t = int(n ** beta); p = t - (t % (2 * n)) + 1
    if p <= 2 * n: p += 2 * n
    while True:
        if p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)) and (p - 1) % (2 * n) == 0:
            return p
        p += 2 * n

def proot(p):
    fac, m, d = [], p - 1, 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac): return g

def run(n, beta):
    p = find_prime(n, beta); g = proot(p)
    h = pow(g, (p - 1) // (2 * n), p); zeta = h
    muN = np.array([pow(h, 2 * j, p) for j in range(n)], dtype=np.int64)
    seen = np.zeros(p, dtype=bool); reps = []
    for b in range(1, p):
        if seen[b]: continue
        seen[(b * muN) % p] = True; reps.append(b)
    reps = np.array(reps, dtype=np.int64)
    w = np.exp(2j * np.pi / p)
    def eta(bv): return (w ** ((np.outer(bv, muN)) % p)).sum(axis=1)
    eb = eta(reps)
    re = eb.real
    nrm2 = np.abs(eb) ** 2
    # for each rep b, the sign of Re eta along its zeta-orbit (length = order of zeta in F_p^*/<...>)
    # we only need adjacent triples; check fraction of HEAVY reps (top 10% by ||eta||) whose
    # Re eta_{zeta^{-1}b}, Re eta_b, Re eta_{zeta b} are all the SAME sign.
    re_zb = eta((zeta * reps) % p).real
    re_zib = eta((pow(zeta, p - 2, p) * reps) % p).real
    thr = np.quantile(nrm2, 0.90)
    heavy = nrm2 >= thr
    same3 = (np.sign(re_zib) == np.sign(re)) & (np.sign(re) == np.sign(re_zb))
    return dict(n=n, p=p,
                heavy_same3=float(np.mean(same3[heavy])),
                all_same3=float(np.mean(same3)),
                heavy_meannrm=float(np.mean(nrm2[heavy])),
                all_meannrm=float(np.mean(nrm2)))

if __name__ == "__main__":
    print("=== orbit-sign coherence on heavy frequencies (Re eta along zeta-orbit, 3 consecutive) ===")
    print(f"{'n':>4} {'p':>9} {'heavy_same3':>11} {'all_same3':>10} {'heavyNrm/allNrm':>15}")
    for a in range(3, 7):
        n = 2 ** a
        r = run(n, 4)
        print(f"{r['n']:>4} {r['p']:>9} {r['heavy_same3']:>11.3f} {r['all_same3']:>10.3f} "
              f"{r['heavy_meannrm']/r['all_meannrm']:>15.3f}")
    print()
    print("READ: heavy_same3 ~ 1.0 => heavy freqs have sign-constant Re eta along the orbit")
    print("      => cross-signs coherent => no mixed-sign heavy mass => iterated halving blocked.")
