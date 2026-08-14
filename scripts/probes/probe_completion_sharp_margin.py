#!/usr/bin/env python3
"""
PROBE: the completion-method's SHARP sub-sqrt(q) bound and its THIN-REGIME COLLAPSE.

In-tree `mul_norm_eta_torsion_le` proves (axiom-clean):
    t * |eta_psi(G,b)|  <=  (t-1)*sqrt(q) + 1        [t = (q-1)/d]
=> the SHARP form, never threaded to a standalone theorem:
    |eta|  <=  sqrt(q) - (sqrt(q)-1)/t .

CLAIM A (sharpness holds): for the d-torsion subgroup G (n=|G|=(q-1)/t actually d-torsion
  has |G|=d when d|q-1; here G = mu_n the n-th roots of unity, t=(q-1)/n), every nonzero b:
      |eta| <= sqrt(q) - (sqrt(q)-1)/t   (strictly below the classical sqrt(q) anchor).

CLAIM B (thin-regime COLLAPSE = refutation-with-mechanism): the completion MARGIN
      margin(t) := (sqrt(q)-1)/t = n*(sqrt(q)-1)/(q-1) ~ n/sqrt(q)
  VANISHES (as a fraction of sqrt(q): margin/sqrt(q) ~ n/q -> 0) in the PRIZE regime
  q = n^beta, beta in {4,5}. So the completion anchor CANNOT reach the prize bound
  sqrt(n log(p/n)) <<< sqrt(q): the sharp completion bound stays ~ sqrt(q), beaten only by
  an o(1) fraction. PRECISELY delimits why classical completion is non-proving for CORE.

NEVER validates on n=q-1 (full group). PROPER thin mu_n only. Multiple structured primes.
"""
import cmath, math

def primitive_root(p):
    # smallest generator of F_p^*
    fac = []
    phi = p - 1
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no gen")

def eta_max(p, n):
    """max over b!=0 of |sum_{x in mu_n} e_p(b x)|, mu_n = n-th roots of unity in F_p^*."""
    assert (p-1) % n == 0, "n must divide p-1"
    g = primitive_root(p)
    t = (p-1)//n
    # mu_n = { g^(t*k) mod p : k=0..n-1 }
    base = pow(g, t, p)
    mu = []
    v = 1
    for _ in range(n):
        mu.append(v)
        v = (v*base) % p
    assert len(set(mu)) == n
    w = cmath.exp(2j*math.pi/p)
    best = 0.0
    for b in range(1, p):
        s = sum(w**((b*x) % p) for x in mu)
        a = abs(s)
        if a > best:
            best = a
    return best, t

def run():
    sqrt = math.sqrt
    # structured + generic primes, p == 1 mod n, p >> n^3 where feasible, PROPER thin mu_n
    cases = [
        # (p, n)  -- p == 1 mod n, n a 2-power (thin), n << p
        (97, 4), (97, 8), (193, 8), (257, 16), (257, 8),
        (641, 8), (641, 16), (769, 16), (12289, 16), (12289, 32),
        (40961, 16), (40961, 32), (40961, 64),
        (65537, 16), (65537, 32), (65537, 64), (65537, 128),
    ]
    print(f"{'p':>7} {'n':>5} {'t':>7} {'|eta|max':>10} {'sqrtq':>9} "
          f"{'sharp_bd':>9} {'margin':>8} {'marg/sq':>8} {'A_ok':>5} {'beta':>5}")
    allA = True
    for p, n in cases:
        if (p-1) % n != 0:
            continue
        emax, t = eta_max(p, n)
        sq = sqrt(p)
        margin = (sq - 1)/t
        sharp = sq - margin
        A_ok = emax <= sharp + 1e-9          # sharp completion bound holds
        allA = allA and A_ok
        beta = math.log(p)/math.log(n)
        print(f"{p:>7} {n:>5} {t:>7} {emax:>10.4f} {sq:>9.4f} "
              f"{sharp:>9.4f} {margin:>8.4f} {margin/sq:>8.5f} {str(A_ok):>5} {beta:>5.2f}")
    print()
    print("CLAIM A (sharp bound |eta| <= sqrt(q) - (sqrt(q)-1)/t holds everywhere):", allA)
    print("CLAIM B (margin/sqrt(q) = (1-1/sqrt(q))/t ~ n/q -> 0 as beta grows): see marg/sq column")
    print("=> thinner n (smaller t-fraction... actually LARGER t) => margin/sqrt(q) ~ n/q SHRINKS")
    print("   the SHARP completion bound stays ~ sqrt(q); CANNOT reach prize sqrt(n log(p/n)).")

if __name__ == "__main__":
    run()
