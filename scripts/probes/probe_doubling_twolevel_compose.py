#!/usr/bin/env python3
"""
#444 -- TWO-LEVEL COMPOSITION of the doubling-mass halving (NON-moment structural lever).

See header discussion below. Key question: does plusMass <= (1/2)q|G| (proven, single level,
DilationDoublingMassHalf) ITERATE to plus2Mass <= (1/4)q|G| at depth 2?  If yes -> geometric
deep-descent control (big). If no (positive sign-correlation) -> refutation-with-mechanism on the
MASS side, matching survivor-honesty's COUNT no-recursion finding.

EFFICIENCY: coset-reduced. eta_b is constant on mu_n-cosets of F_p^*, so we evaluate periods only
on coset reps (there are (p-1)/n of them) and weight by coset size n. We use cosets of mu_{2n} for
the cross-sign pairing to be coset-coherent. Exact-ish: complex roots of unity (imMax reported to
confirm reality from negation-closure). Prize-band: p ~ n^4, PROPER thin mu_n (NEVER n=q-1).
"""
import numpy as np

def find_prime(n, beta):
    target = int(n ** beta)
    p = target - (target % (2 * n)) + 1
    if p <= 2 * n:
        p += 2 * n
    while True:
        if p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
            if (p - 1) % (2 * n) == 0:
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
    raise RuntimeError("no primitive root")

def run(n, beta):
    p = find_prime(n, beta)
    g = primitive_root(p)
    h = pow(g, (p - 1) // (2 * n), p)      # order 2n
    zeta = h
    zinv = pow(zeta, p - 2, p)
    muN = np.array([pow(h, 2 * j, p) for j in range(n)], dtype=np.int64)   # mu_n

    # coset reps of mu_n in F_p^*: b is a rep iff b == min of its mu_n-coset.
    # cheap: iterate b=1..p-1, mark whole coset, collect first-seen reps.
    seen = np.zeros(p, dtype=bool)
    reps = []
    for b in range(1, p):
        if seen[b]:
            continue
        coset = (b * muN) % p
        seen[coset] = True
        reps.append(b)
    reps = np.array(reps, dtype=np.int64)   # (p-1)/n reps

    # eta_b = sum_{x in muN} e_p(b x).  Compute for the b-values we need:
    #   for each rep b: need eta_b, eta_{zeta b}, eta_{zinv b}.
    # zeta b and zinv b live in OTHER cosets but we just compute directly per needed b.
    w = np.exp(2j * np.pi / p)
    def eta(bv):
        # bv: array of b's; returns eta_b
        # eta_b = sum_x w^{(b x) mod p}
        ph = (np.outer(bv, muN)) % p      # (len(bv), n)
        return (w ** ph).sum(axis=1)

    eb = eta(reps)
    ezb = eta((zeta * reps) % p)
    ezib = eta((zinv * reps) % p)
    imMax = float(np.max(np.abs(eb.imag)))

    re_b, re_zb, re_zib = eb.real, ezb.real, ezib.real
    s1 = re_b * re_zb           # cross-sign at zeta
    s2 = re_zib * re_b          # cross-sign at zeta^{-1} (other neighbor)
    cm = np.abs(eb) * np.abs(ezb)     # ||eta_b|| ||eta_{zeta b}||

    wgt = n                      # each rep stands for n frequencies (its mu_n coset)
    q = p
    Gcard = n
    total = cm.sum() * wgt
    plus1 = cm[s1 >= 0].sum() * wgt
    plus2 = cm[(s1 >= 0) & (s2 >= 0)].sum() * wgt
    cap_half = 0.5 * q * Gcard
    cap_quarter = 0.25 * q * Gcard
    f_s1 = float(np.mean(s1 >= 0))
    f_s2 = float(np.mean(s2 >= 0))
    f_both = float(np.mean((s1 >= 0) & (s2 >= 0)))
    return dict(n=n, beta=beta, p=p, imMax=imMax,
                tot_qG=total / (q * Gcard),
                p1_half=plus1 / cap_half,
                p2_quarter=plus2 / cap_quarter,
                p2_over_p1=plus2 / plus1 if plus1 > 0 else float('nan'),
                f_both=f_both, f_s1=f_s1, f_s2=f_s2,
                indep=f_s1 * f_s2)

if __name__ == "__main__":
    print("=== TWO-LEVEL doubling-mass composition (cond A: + at zeta AND + at zeta^{-1}) ===")
    print("PROPER thin mu_n, p~n^beta, 2n|p-1, NEVER n=q-1. p2/.25qG>1 => no 2nd halving.")
    print(f"{'n':>4} {'beta':>4} {'p':>8} {'imMax':>8} {'tot/qG':>7} {'p1/.5qG':>8} "
          f"{'p2/.25qG':>9} {'p2/p1':>7} {'f_both':>7} {'f1*f2':>7}")
    for beta in (4,):
        for a in range(3, 7):    # n=8..64 (p~n^4: 64^4=1.6e7 ok)
            n = 2 ** a
            try:
                r = run(n, beta)
            except Exception as e:
                print(f"{n:>4} {beta:>4}  ERR {type(e).__name__}: {e}")
                continue
            print(f"{r['n']:>4} {r['beta']:>4} {r['p']:>8} {r['imMax']:>8.1e} "
                  f"{r['tot_qG']:>7.3f} {r['p1_half']:>8.3f} {r['p2_quarter']:>9.3f} "
                  f"{r['p2_over_p1']:>7.3f} {r['f_both']:>7.3f} {r['indep']:>7.3f}")
    print()
    print("READ: p2/p1 ~ 0.5 + f_both~f1*f2 => independent => second halving COMPOSES (geom cap).")
    print("      p2/p1 ~ 1.0 + f_both>>f1*f2 => positive sign-correlation => NO 2nd halving (wall).")
