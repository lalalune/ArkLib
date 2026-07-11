#!/usr/bin/env python3
"""
probe_dooriv_sixth_connected_cumulant.py  (#444, door-(iv) Lane 1)

CONTEXT / deconflict: commit 8b2df98a5 proved the period field {eta_b} is Gaussian to FULL 4th
order (off-diagonal connected 4-pt cumulant T4 == 0, diagonal = dead E2). Its OWN conclusion:
"Any crack must live at 6th order+ or outside the moment hierarchy."  3rd order telescopes to
p*Z3 (zero-sum triples, known dead). So the FIRST place a genuinely new door-(iv) phase-structure
object could appear is the **6th-order connected cumulant** of the (real, even) period field.

This probe asks the decisive door-(iv) question at 6th order:

  Q. Is the 6th connected cumulant kappa6 of the period marginal eta_b (b ranged over the
     multiplicative quotient) ZERO (=> Gaussian past 4th order, field is a Wick/Gaussian object
     to 6th, refutes the "crack at 6th" hope) or NON-ZERO and GROWING with n (=> a genuine
     non-moment phase object survives, the door-(iv) lever lives here)?

We compute, EXACTLY in integers mod p for the index arithmetic and exact complex doubles for eta:
  eta_b = sum_{x in mu_n} e_p(b*x),  real since 4 | n (mu_n closed under negation).

Marginal connected cumulants of the REAL random variable X = eta_b (b uniform over nonzero
quotient reps), centered (mean 0 by character orthogonality for b != 0):
  m2 = E[X^2]            (= n exactly, Plancherel)
  m4 = E[X^4]
  m6 = E[X^6]
  kappa4 = m4 - 3 m2^2                       (Gaussian => 0)
  kappa6 = m6 - 15 m4 m2 + 30 m2^3           (Gaussian => 0)   [standardized: for var s2,
                                              kappa6 = m6 - 15 m4 s2 + 30 s2^3 with mean 0]

Decisive classification (rule-5 honesty):
  - normalized excess kurtosis  g2 = kappa4 / m2^2          (Gaussian => 0)
  - normalized 6th cumulant      g3 = kappa6 / m2^3          (Gaussian => 0)
  If |g3| -> 0 as n grows  => field is Gaussian to 6th order too; the "crack at 6th" hope is
     DEAD; cracks must move to 8th+ or leave the moment hierarchy entirely.  HONEST REFUTATION.
  If |g3| stays bounded-away-from-0 or GROWS => genuine 6th-order non-Gaussian phase structure;
     door-(iv) lever candidate. PROBE DEEPER before any claim.

We sweep n=16..256 over multiple structured primes (Fermat-type + generic p == 1 mod n,
p >> n^3 prize regime) and check stability / trend.  Probe-first; nothing formalized unless real.
"""
import numpy as np
from math import sqrt, gcd

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prim_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    phi = p-1
    fac = set()
    t = phi; d = 2
    while d*d <= t:
        while t % d == 0: fac.add(d); t //= d
        d += 1
    if t > 1: fac.add(t)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no prim root")

def find_prime(n, beta, fermat=False):
    """find prime p == 1 mod n, p ~ n^beta (prize regime, p >> n^3)."""
    if fermat:
        # Fermat primes 65537 etc only support n | 2^16; use when n small
        for k in (16,8,4):
            P = (1 << (1 << 4)) + 1  # 65537
            if P % n == 1 and isprime(P) and P > n**3:
                return P
    target = int(round(n**beta))
    # search upward for p == 1 mod n, prime, > n^3
    lo = max(target, n**3 + 1)
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while True:
        if isprime(p):
            return p
        p += n

def periods(n, p, max_reps=200000, seed=12345):
    """eta_b over MULTIPLICATIVE QUOTIENT reps (b != 0). eta_b depends on b only through its
       coset b*mu_n; there are (p-1)/n cosets. If that exceeds max_reps we take a uniform random
       SAMPLE of distinct cosets (cumulants are coset-statistics; a large uniform sample is an
       unbiased estimator -- honest for trend, flagged as sampled).
       Returns (etas, sampled_bool)."""
    g = prim_root(p)
    m = (p-1)//n                                   # number of cosets = (p-1)/n
    H = np.array([pow(g, (m*j) % (p-1), p) for j in range(n)], dtype=np.int64)  # mu_n elements
    twopi_over_p = 2.0*np.pi/p
    if m <= max_reps:
        ts = list(range(m))
        sampled = False
    else:
        rng = np.random.default_rng(seed)
        ts = rng.choice(m, size=max_reps, replace=False)
        sampled = True
    # OVERFLOW-SAFE: for prize-regime p ~ n^4 (~4.3e9 at n=256), b*H can exceed int64 (1.8e19 >
    # 9.2e18). Reduce mod p in Python-int / object dtype so the residue is EXACT (codex P2 fix).
    Hobj = H.astype(object)
    etas = np.empty(len(ts))
    for i, t in enumerate(ts):
        b = pow(g, int(t), p)                      # one rep per coset (g^t)
        res = (int(b) * Hobj) % p                   # exact bignum modular reduction, no wraparound
        ang = twopi_over_p * res.astype(np.float64)
        etas[i] = np.cos(ang).sum()                # imaginary part cancels (eta real)
    return etas, sampled

def cumulants(x):
    x = np.asarray(x, dtype=float)
    mu = x.mean()
    xc = x - mu
    m2 = (xc**2).mean()
    m4 = (xc**4).mean()
    m6 = (xc**6).mean()
    k4 = m4 - 3*m2**2
    k6 = m6 - 15*m4*m2 + 30*m2**3
    g2 = k4 / m2**2 if m2 > 0 else float('nan')
    g3 = k6 / m2**3 if m2 > 0 else float('nan')
    return dict(mean=mu, m2=m2, m4=m4, m6=m6, k4=k4, k6=k6, g2=g2, g3=g3)

def main():
    print("# door-(iv) 6th-order connected cumulant of the period field {eta_b}")
    print("# Gaussian => g2=g3=0. crack-at-6th hope alive only if |g3| bounded-away / growing.\n")
    print(f"{'n':>5} {'p':>14} {'beta':>5} {'#reps':>8} {'m2/n':>8} {'g2(kurt)':>10} {'g3(6th)':>12} {'verdict':>10}")
    rows = []
    for n in (16, 32, 64, 128, 256):
        beta = 4.0
        p = find_prime(n, beta)
        et, sampled = periods(n, p)
        c = cumulants(et)
        verdict = "GAUSS" if abs(c['g3']) < 0.05 else "NONGAUSS?"
        smk = "~" if sampled else " "
        print(f"{n:>5} {p:>14} {beta:>5.1f} {smk}{len(et):>7} {c['m2']/n:>8.4f} {c['g2']:>10.4f} {c['g3']:>12.4f} {verdict:>10}")
        rows.append((n, c['g2'], c['g3']))
    print()
    # trend on g3 (6th cumulant): is it -> 0 (gaussian, refute) or bounded-away/growing (lever)?
    print("## TREND (n -> g3):")
    for n, g2, g3 in rows:
        print(f"  n={n:>4}  g2={g2:+.5f}  g3={g3:+.5f}")
    g3s = [abs(r[2]) for r in rows]
    if g3s[-1] < 0.5*g3s[0] and g3s[-1] < 0.05:
        print("\nVERDICT: |g3| -> 0 with n. PERIOD FIELD IS GAUSSIAN TO 6th ORDER.")
        print("  => the 'crack lives at 6th order' hope is DEAD. cracks must move to 8th+ or")
        print("     leave the moment hierarchy. door-(iv) 6th-cumulant lever REFUTED.")
    elif max(g3s) > 0.1 and g3s[-1] >= 0.5*max(g3s):
        print("\nVERDICT: |g3| bounded-away-from-0 / not collapsing. 6th-order non-Gaussian")
        print("  phase structure SURVIVES. door-(iv) lever candidate -- probe deeper (lag-resolved,")
        print("  per-worst-b, sign-structure) before any formalization.")
    else:
        print("\nVERDICT: ambiguous/finite-size; need larger n or more primes. NO CLAIM.")

if __name__ == "__main__":
    main()
