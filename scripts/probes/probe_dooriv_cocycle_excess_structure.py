#!/usr/bin/env python3
"""
probe_dooriv_cocycle_excess_structure.py  (#444, door-(iv) Lane 1 — follow-up to dispersion-magnitude)

The dispersion-magnitude probe (committed c298763ff) found the real Jacobi-cocycle sup is LARGER than a
random-iid-phase surrogate (real/iid = 1.15..1.44). That EXCESS is the only remaining place a cocycle-
specific signal could hide. This probe asks whether the excess is:

  (A) a structureless extreme-value artifact (the sup of a slightly heavier-tailed but still essentially
      random |eta_b|^2 distribution) — in which case it is door (iii) (extreme-value=BGK, DEAD), OR
  (B) a SYSTEMATIC second-moment / correlation effect of the genuine Jacobi sums — in which case there
      is residual multiplicative structure in the |eta_b|^2 field that a non-moment method might grip.

The clean discriminator is the **second moment of the period field** vs the iid prediction, and the
**excess kurtosis** of the |eta_b| distribution:

  * For n iid unit phases, E[|S|^2] = n exactly, and |S|^2/n -> Exp(1) (so |S| is Rayleigh): the
    distribution of |eta_b|^2 is asymptotically exponential with mean n, kurtosis of |eta_b| -> Rayleigh
    (excess kurtosis ~ 0.245), and the sup over m draws ~ sqrt(n*log m).
  * If the real |eta_b|^2 field has E[|eta_b|^2] = n (Parseval — it MUST, this is forced) but a DIFFERENT
    higher-moment / tail shape, the deviation is the cocycle's fingerprint. We measure:
       - mean of |eta_b|^2  (must be ~ n by Parseval — sanity check)
       - normalized 4th moment  E[|eta|^4]/E[|eta|^2]^2   (iid Rayleigh-modulus -> 2.0 exactly)
       - excess kurtosis of |eta_b|
       - the tail exponent of P(|eta_b| > t) in the upper tail (where the sup lives)
    against the iid surrogate's SAME statistics, head to head.

VERDICT LOGIC:
  - real moments ~ iid moments (ratios -> 1, tails coincide)  => excess is a tiny finite-n extreme-value
    fluctuation with NO distributional signature => door (iii), DEAD. The +15-44% sup excess is just the
    sup picking up a slightly fatter finite-n tail of the SAME family.
  - real 4th moment / kurtosis / tail SYSTEMATICALLY exceeds iid and the gap GROWS or stabilizes with n
    => a genuine heavy-tail multiplicative signature => residual structure; formalize the OBSERVED fact.

This is a CALIBRATION/refutation probe. CORE stays open either way.

Method: exact arithmetic, PROPER mu_n, p ~ n^4 >> n^3, multiple primes, never n=q-1, uniform coset sample.
"""
import cmath, math, random, statistics
random.seed(444)

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(n, ratio):
    lo = int(n ** ratio); k = lo // n + 1
    while True:
        p = k*n + 1
        if is_prime(p): return p
        k += 1

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = set(); m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac): return g
    raise RuntimeError

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    e = []; cur = 1
    for _ in range(n):
        e.append(cur); cur = cur*h % p
    return g, e

def period_field(p, n, mu, reps):
    tp = 2.0*math.pi/p; mags2 = []
    for b in reps:
        s = 0j
        for x in mu:
            s += cmath.exp(1j*tp*((b*x) % p))
        mags2.append((s.real*s.real + s.imag*s.imag))
    return mags2  # |eta_b|^2

def iid_field(n, m):
    out = []
    for _ in range(m):
        s = 0j
        for _ in range(n):
            s += cmath.exp(2j*math.pi*random.random())
        out.append(s.real*s.real + s.imag*s.imag)
    return out

def stats(mags2, n):
    m1 = statistics.mean(mags2)              # ~ n by Parseval
    mags = [math.sqrt(v) for v in mags2]
    mm = statistics.mean(mags)
    var = statistics.pvariance(mags)
    sd = math.sqrt(var) if var > 0 else 1e-12
    m4mod = statistics.mean(v*v for v in mags2) / (m1*m1) if m1 > 0 else float('nan')  # E|eta|^4/E|eta|^2^2
    # excess kurtosis of |eta|
    kurt = statistics.mean(((x-mm)/sd)**4 for x in mags) - 3.0
    mx = max(mags)
    # upper-tail count fraction above 0.7*max (where the sup neighborhood sits)
    thr = 0.7*mx
    tailfrac = sum(1 for x in mags if x >= thr)/len(mags)
    return dict(meanSq=m1/n, m4norm=m4mod, exKurt=kurt, supOverSqrtN=mx/math.sqrt(n), tailfrac=tailfrac)

def main():
    print("="*92)
    print("COCYCLE EXCESS STRUCTURE — is the real>iid sup excess a moment signature or extreme-value noise?")
    print("iid Rayleigh-modulus reference: meanSq=1.0, m4norm=2.0, exKurt~0.245")
    print("="*92)
    print(f"{'n':>4} {'p':>11} {'m':>7} | {'meanSq_r':>8} {'meanSq_i':>8} | {'m4_r':>6} {'m4_i':>6} "
          f"{'m4r/m4i':>7} | {'kurt_r':>7} {'kurt_i':>7} | {'tail_r':>7} {'tail_i':>7}")
    rows = []
    CAP = 16000
    for n in [16, 32, 64, 128]:
        for ratio in (4.0, 4.3):
            p = find_prime(n, ratio); g, mu = subgroup(p, n)
            ncos = (p-1)//n
            js = list(range(ncos))
            if ncos > CAP: js = random.sample(js, CAP)
            reps = [pow(g, j, p) for j in js]
            m = len(reps)
            rf = period_field(p, n, mu, reps)
            xf = iid_field(n, m)
            sr = stats(rf, n); si = stats(xf, n)
            rows.append((n, ratio, sr, si))
            print(f"{n:>4} {p:>11} {m:>7} | {sr['meanSq']:>8.3f} {si['meanSq']:>8.3f} | "
                  f"{sr['m4norm']:>6.3f} {si['m4norm']:>6.3f} {sr['m4norm']/si['m4norm']:>7.3f} | "
                  f"{sr['exKurt']:>7.3f} {si['exKurt']:>7.3f} | {sr['tailfrac']:>7.4f} {si['tailfrac']:>7.4f}")

    print("\n" + "-"*92)
    print("Q  is the real 4th-moment ratio (m4_r/m4_i) systematically > 1 and stable/growing with n?")
    by_n = {}
    for n, ratio, sr, si in rows:
        by_n.setdefault(n, []).append(sr['m4norm']/si['m4norm'])
    ns = sorted(by_n)
    for n in ns:
        a = sum(by_n[n])/len(by_n[n])
        print(f"   n={n:>4}  mean m4_r/m4_i = {a:.4f}")
    first = sum(by_n[ns[0]])/len(by_n[ns[0]]); last = sum(by_n[ns[-1]])/len(by_n[ns[-1]])
    if last > 1.03 and last >= first*0.97:
        verdict = ("SYSTEMATIC heavy-tail signature (real 4th moment exceeds iid, persists) => residual\n"
                   "   multiplicative structure in |eta|^2 field; formalize the OBSERVED fact (Lane-1 lever?)")
    elif abs(last-1.0) <= 0.03:
        verdict = ("real ~ iid moments (4th-moment ratio -> 1): the sup excess is a finite-n extreme-value\n"
                   "   fluctuation of the SAME Rayleigh family, NO distributional signature => door (iii) DEAD.")
    else:
        verdict = (f"ratio {last:.3f} drifting toward 1: excess is shrinking finite-n effect => door (iii).")
    print(f"\nVERDICT: {verdict}")
    print("\nmeanSq sanity: both columns must be ~1.000 (Parseval forces E|eta_b|^2 = n). Deviation = bug.")
    print("="*92)

if __name__ == "__main__":
    main()
