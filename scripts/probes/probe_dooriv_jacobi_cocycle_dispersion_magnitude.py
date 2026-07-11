#!/usr/bin/env python3
"""
probe_dooriv_jacobi_cocycle_dispersion_magnitude.py  (#444, door-(iv) Lane 1)

DIRECTLY measure the named open object `JacobiCocycleDispersion` (the SINGLE live
missing theorem per _JacobiCocycleDispersion.lean / Shaw's tetrachotomy).

The dispersion file proves only the two ENDPOINTS of the worst-case sup:
  * floor (Parseval / avg_le_sup):  M >= sqrt(n)
  * trivial-cocycle baseline:        M = n            (max concentration, when the
                                                       Jacobi cocycle is a coboundary)
and pins the prize to: does the ACTUAL (non-trivial) Jacobi cocycle DISPERSE the
projective-Fourier sup from the trivial concentration `n` down to `sqrt(n*log m)`?

No committed probe MEASURES this dispersion magnitude as a function of n. This probe
does exactly that, in the prize regime, and asks the only question that matters for a
non-moment route:

  Q1 (CALIBRATION): does the real-cocycle sup M sit STRICTLY BELOW the trivial
     concentration n, by a multiplicative factor that GROWS with n?  (If M/n -> 0,
     the cocycle demonstrably disperses; if M/n -> const>0, the prize is in danger.)
  Q2 (SCALING): does M track sqrt(n*log m) [prize], or sqrt(n)*n^delta [super-prize],
     i.e. fit M = c * n^alpha and read alpha.  alpha=0.5 => prize-consistent;
     alpha>0.5 => the dispersion is INCOMPLETE and the wall is real at this n.
  Q3 (NON-MOMENT WITNESS): is the dispersion sensitive to the COCYCLE (multiplicative
     structure) and NOT reproduced by an additive/iid surrogate with the same |theta|=1
     magnitudes but random phases?  If the real cocycle disperses MORE (lower M) than the
     iid-phase surrogate, that excess dispersion is exactly the non-moment lever the brief
     wants.  If it disperses the SAME or LESS, the cocycle gives no exploitable edge.

Honest framing: this is a CALIBRATION/refutation probe of the dispersion object, not a
proof of CORE. A clean "alpha hugs 0.5 and real << iid" would localize a real lever; a
"alpha > 0.5" or "real ~ iid" outcome is a refutation-with-mechanism (logged to DISPROOF).

Method: exact arithmetic. mu_n = unique order-n multiplicative subgroup of F_p* (p prime,
p = 1 mod n, prize regime p ~ n^4 >> n^3, multiple structured primes, NEVER n=q-1).
  eta_b = sum_{x in mu_n} e_p(b*x)   (the period; b ranges over coset reps F_p*/mu_n)
  M = max_{b != 0} |eta_b|.
The trivial-cocycle baseline n and the floor sqrt(n) bracket M; we read where M lives.

The iid surrogate: replace the n genuine roots' phase-sum by sum of n unit phases
exp(2*pi*i*U_k), U_k iid uniform — same count, same |term|=1, destroyed multiplicative
structure. Its sup over m independent draws is the "no-cocycle-structure" control.
"""
import cmath
import math
import random

random.seed(444)

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(n, target_ratio):
    """smallest prime p = 1 mod n with p >= n^target_ratio (prize regime ratio~4)."""
    lo = int(n ** target_ratio)
    # round up to 1 mod n
    k = (lo // n) + 1
    while True:
        p = k * n + 1
        if is_prime(p):
            return p
        k += 1

def primitive_root(p):
    """a generator of F_p*."""
    if p == 2: return 1
    phi = p - 1
    # factor phi
    fac = set()
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no prim root")

def subgroup_mu_n(p, n):
    """the unique order-n subgroup of F_p* (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # element of order n
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur)
        cur = (cur * h) % p
    assert len(set(elts)) == n, "subgroup degenerate"
    return g, elts

def period_sup(p, n, mu, coset_reps):
    """M = max over b in coset_reps of |sum_{x in mu} e_p(b x)|, and the full distribution mean."""
    twopi_over_p = 2.0 * math.pi / p
    best = 0.0
    vals = []
    for b in coset_reps:
        s = 0.0 + 0.0j
        for x in mu:
            ang = twopi_over_p * ((b * x) % p)
            s += cmath.exp(1j * ang)
        a = abs(s)
        vals.append(a)
        if a > best:
            best = a
    mean = sum(vals) / len(vals)
    return best, mean, vals

def iid_surrogate_sup(n, m_draws):
    """control: sup over m_draws of |sum of n iid unit phases| (no multiplicative structure)."""
    best = 0.0
    for _ in range(m_draws):
        s = 0.0 + 0.0j
        for _ in range(n):
            u = random.random()
            s += cmath.exp(2j * math.pi * u)
        a = abs(s)
        if a > best:
            best = a
    return best

def coset_representatives(p, n, g, cap):
    """representatives of F_p*/mu_n.  mu_n = <g^((p-1)/n)>, so cosets are g^j*mu_n for
    j=0..(p-1)/n-1; a rep is g^j.  Sample up to `cap` reps (exclude b=0 trivially;
    b ranges over nonzero classes; the period only depends on the coset since mu absorbs
    the subgroup).  We sample j uniformly to avoid scan-stride artifacts (NOTE lesson)."""
    num_cosets = (p - 1) // n
    js = list(range(num_cosets))
    if num_cosets > cap:
        js = random.sample(js, cap)
    reps = [pow(g, j, p) for j in js]
    return reps, num_cosets

def main():
    print("=" * 78)
    print("JACOBI COCYCLE DISPERSION MAGNITUDE — direct measurement of the open object")
    print("prize regime: proper mu_n, p ~ n^4 >> n^3, structured + generic primes, never q-1")
    print("=" * 78)
    print(f"{'n':>4} {'p':>12} {'#cos':>8} {'M':>8} {'M/sqrt(n)':>10} {'M/n':>7} "
          f"{'sqrt(nlogm)':>11} {'M/target':>9} {'iidSup':>8} {'real/iid':>8}")
    rows = []
    # prize regime ratios; a couple per n to test prime-stability of the dispersion
    configs = []
    for n in [16, 32, 64, 128]:
        configs.append((n, 4.0))
        configs.append((n, 4.3))
    CAP = 20000  # max cosets sampled (exact period each)
    for n, ratio in configs:
        p = find_prime(n, ratio)
        g, mu = subgroup_mu_n(p, n)
        reps, num_cos = coset_representatives(p, n, g, CAP)
        M, mean, vals = period_sup(p, n, mu, reps)
        m_eff = min(num_cos, CAP)  # number of frequencies actually in the sup
        logm = math.log(max(m_eff, 2))
        target = math.sqrt(n * logm)
        iidsup = iid_surrogate_sup(n, m_eff)
        rows.append((n, ratio, p, num_cos, M, M / math.sqrt(n), M / n,
                     target, M / target, iidsup, M / iidsup if iidsup > 0 else float('nan'),
                     mean))
        print(f"{n:>4} {p:>12} {num_cos:>8} {M:>8.3f} {M/math.sqrt(n):>10.3f} "
              f"{M/n:>7.3f} {target:>11.3f} {M/target:>9.3f} {iidsup:>8.3f} "
              f"{(M/iidsup if iidsup>0 else float('nan')):>8.3f}")

    # ---- Q1: does M/n shrink with n? (cocycle demonstrably disperses below trivial) ----
    print("\n" + "-" * 78)
    print("Q1  dispersion below trivial concentration n  (M/n by n):")
    by_n = {}
    for r in rows:
        by_n.setdefault(r[0], []).append(r[6])
    ns = sorted(by_n)
    for n in ns:
        avg = sum(by_n[n]) / len(by_n[n])
        print(f"    n={n:>4}  mean M/n = {avg:.4f}")
    mn_first = sum(by_n[ns[0]]) / len(by_n[ns[0]])
    mn_last = sum(by_n[ns[-1]]) / len(by_n[ns[-1]])
    q1 = "DISPERSES (M/n -> 0)" if mn_last < mn_first * 0.7 else \
         ("PARTIAL" if mn_last < mn_first else "NO DISPERSION (M/n flat/up)")
    print(f"    => Q1 verdict: {q1}   ({mn_first:.4f} -> {mn_last:.4f})")

    # ---- Q2: fit M = c n^alpha (alpha=0.5 prize, >0.5 wall survives at this n) ----
    print("\nQ2  scaling exponent  M ~ c * n^alpha  (least squares on log-log, per ratio):")
    import statistics
    for ratio in sorted(set(r[1] for r in rows)):
        pts = [(math.log(r[0]), math.log(r[4])) for r in rows if r[1] == ratio]
        xb = statistics.mean(x for x, _ in pts)
        yb = statistics.mean(y for _, y in pts)
        num = sum((x - xb) * (y - yb) for x, y in pts)
        den = sum((x - xb) ** 2 for x, _ in pts)
        alpha = num / den if den else float('nan')
        print(f"    ratio={ratio}: alpha = {alpha:.4f}  "
              f"({'prize-consistent (~0.5)' if 0.40 <= alpha <= 0.60 else 'OFF-PRIZE'})")

    # ---- Q3: real cocycle vs iid-phase surrogate (the non-moment lever test) ----
    print("\nQ3  real/iid sup ratio  (does the multiplicative cocycle disperse MORE than random phases?):")
    for n in ns:
        ratios_ri = [r[10] for r in rows if r[0] == n]
        avg = sum(ratios_ri) / len(ratios_ri)
        verdict = ("real disperses LESS (no edge)" if avg > 1.05 else
                   "real ~ iid (cocycle gives NO non-moment edge)" if avg > 0.95 else
                   "real disperses MORE (POTENTIAL non-moment lever!)")
        print(f"    n={n:>4}  mean real/iid = {avg:.4f}   {verdict}")
    print("\nINTERPRETATION KEY:")
    print("  - Q1 DISPERSES + Q2 alpha~0.5 + Q3 real~iid  => the dispersion is REAL but is just")
    print("    the generic sqrt-cancellation of n unit phases; NO multiplicative edge beyond random")
    print("    => routes back to extreme-value/moment (door iii, DEAD). Refutation-with-mechanism.")
    print("  - Q3 real << iid (ratio<0.95, growing gap)  => the Jacobi cocycle disperses BEYOND")
    print("    random-phase cancellation => a genuine non-moment lever survives (formalize the OBSERVED fact).")
    print("  - Q2 alpha>0.6  => dispersion INCOMPLETE at prize n; the wall is live (consistent with SOTA).")
    print("=" * 78)

if __name__ == "__main__":
    main()
