#!/usr/bin/env python3
"""
TOOL 2 CORRECTION (#444): is the FULL Gauss-sum family trivially flat?  And what is the
PRIZE-RELEVANT phase-flatness?

The previous probe (probe_phaseflatness_residual.py) found maxF/sqrt(m) ~ 1.000 for the FULL
multiplicative family P(b) = sum_{chi!=1} chibar(b) G(chi).  That is suspiciously flat.  REASON
(verify here):  by Gauss-sum / Fourier inversion,
    sum_{chi != chi_0} chibar(b) G(chi) = p * e_p(?) - 1   (a SINGLE additive character)
so |P(b)| is constant = sqrt of a trivial thing -> trivially flat, NOT the prize object.

The PRIZE object is the THIN subgroup period  eta_b = sum_{x in mu_n} e_p(b x), n = 2^mu | (p-1),
m = (p-1)/n cosets.  We test:
  (1) confirm the full-family flatness is the trivial additive-character identity (artifact);
  (2) measure the sup-norm flatness of the PRIZE periods eta_b vs random of the SAME sparsity;
  (3) test the dilation/HD structure on the PRIZE periods (the real question for Tool 2).

Honesty: report ACTUAL numbers.  If the prize periods are NOT 15-20%-flat (just ~ same as random
thin sums = the BGK sqrt(n log m) wall), Tool 2's 'beats random by 15-20% but diffuse' is the
right verdict; if the full-family 1.000 was being mistaken for the prize, that's a correction.
"""
import math, cmath, random

def is_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and is_prime(p):
            return p
        p += n

def primitive_root(p):
    phi = p - 1; factors = set(); nn = phi; d = 2
    while d * d <= nn:
        if nn % d == 0:
            factors.add(d)
            while nn % d == 0: nn //= d
        d += 1
    if nn > 1: factors.add(nn)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, i, p) for i in range(n)]

# ---------------------------------------------------------------------------
# (1) Confirm the full-family flatness is the trivial additive-character identity
# ---------------------------------------------------------------------------
def confirm_trivial_flatness(p):
    """P(b) = sum_{chi != 1} chibar(b) G(chi).  Claim: |P(b)| is constant (= the additive char).
       Identity: sum_{chi} chibar(b) G(chi) = p [b==1?]... we just MEASURE |P(b)| for all b and
       report (min,max) to see if it is flat (constant)."""
    m = p - 1
    g = primitive_root(p)
    dlog = [0] * p; gp = 1
    for t in range(m):
        dlog[gp] = t; gp = gp * g % p
    ax = [cmath.exp(2j * math.pi * x / p) for x in range(p)]
    # G(chi_j) = sum_{x=1}^{p-1} e(j dlog[x]/m) e(x/p)
    G = [0j] * m
    for j in range(m):
        G[j] = sum(cmath.exp(2j * math.pi * j * dlog[x] / m) * ax[x] for x in range(1, p))
    # P(b) for b=1..p-1 (b nonzero); chibar_j(b) = e(-j dlog[b]/m)
    mags = []
    for b in range(1, p):
        s = sum(cmath.exp(-2j * math.pi * j * dlog[b] / m) * G[j] for j in range(1, m))
        mags.append(abs(s))
    return min(mags), max(mags), sum(mags) / len(mags)

# ---------------------------------------------------------------------------
# (2) PRIZE periods eta_b = sum_{x in mu_n} e_p(b x); sup-norm flatness vs random-thin
# ---------------------------------------------------------------------------
def prize_periods(p, n):
    H = subgroup(p, n)
    eta = [0j] * p
    for b in range(p):
        eta[b] = sum(cmath.exp(2j * math.pi * (b * x % p) / p) for x in H)
    return eta, H

def prize_supnorm_vs_random(p, n, trials=200, seed=0):
    """M = max_{b!=0} |eta_b|.  Baseline: random thin sum sum of n random unit phases, the same
       'thin exponential sum' null model; report M and the random max over m=(p-1)/n distinct
       coset-reps (eta is constant on cosets of mu_n so there are m distinct values)."""
    eta, H = prize_periods(p, n)
    m = (p - 1) // n
    # distinct values: one per coset of mu_n in F_p^* ; pick coset reps
    g = primitive_root(p)
    reps = [pow(g, i, p) for i in range(m)]   # coset reps g^0..g^{m-1}
    vals = [abs(eta[r]) for r in reps]
    M = max(vals)
    rms = math.sqrt(sum(v * v for v in vals) / len(vals))
    # random-thin baseline: m i.i.d. sums of n random unit phases; report E[max], scaled
    rng = random.Random(seed)
    rand_max = []
    for _ in range(trials):
        rvals = []
        for _ in range(m):
            s = sum(cmath.exp(2j * math.pi * rng.random()) for _ in range(n))
            rvals.append(abs(s))
        rand_max.append(max(rvals))
    rmean = sum(rand_max) / len(rand_max)
    return M, rms, rmean, m

# ---------------------------------------------------------------------------
# (3) dilation / HD structure on the prize periods (multiplicative shift on b)
# ---------------------------------------------------------------------------
def prize_dilation_corr(p, n):
    """eta is a class function on cosets of mu_n.  Index the m coset values by t (rep g^t).
       eta_t := eta_{g^t}.  Multiplicative dilation lambda on the coset index t -> (lambda t mod m).
       D(lambda) = sum_t eta_t conj(eta_{lambda t}) / sum_t|eta_t|^2  (correlation, in [0,1]).
       HD-doubling = lambda = 2 (chi -> chi^2 dual on the additive frequency)."""
    eta, H = prize_periods(p, n)
    m = (p - 1) // n
    g = primitive_root(p)
    et = [eta[pow(g, t, p)] for t in range(m)]
    denom = sum(abs(v) ** 2 for v in et)
    res = []
    for lam in range(2, m):
        if math.gcd(lam, m) != 1: continue
        s = sum(et[t] * et[(lam * t) % m].conjugate() for t in range(m))
        res.append((abs(s) / denom, lam))
    res.sort(reverse=True)
    return res, m

def run():
    print("=" * 78)
    print("(1) Is the FULL Gauss-sum family P(b)=sum_{chi!=1} chibar(b)G(chi) trivially flat?")
    print("=" * 78)
    for p in [101, 211, 401]:
        mn, mx, av = confirm_trivial_flatness(p)
        print(f"  p={p}: |P(b)| over b=1..p-1  min={mn:.4f} max={mx:.4f} mean={av:.4f}  "
              f"sqrt(p)={math.sqrt(p):.4f}  => {'CONSTANT (trivial additive char)' if mx-mn<1e-6 else 'varies'}")
    print()
    print("=" * 78)
    print("(2) PRIZE subgroup periods eta_b: M=max|eta_b| vs RANDOM-THIN, and the BGK scale")
    print("=" * 78)
    print(f"  {'n':>3} {'p':>9} {'m':>6} {'M=max|eta|':>11} {'RMS':>8} {'rand E[max]':>11} "
          f"{'M/randmax':>9} {'M/sqrt(n)':>9} {'M/sqrt(n ln m)':>14}")
    for n in [8, 16, 32]:
        for lo in ([2003, 20011] if n <= 16 else [4001]):
            p = find_prime_cong1(n, lo)
            M, rms, rmean, m = prize_supnorm_vs_random(p, n, trials=120)
            lnm = math.log(m) if m > 1 else 1.0
            print(f"  {n:>3} {p:>9} {m:>6} {M:>11.4f} {rms:>8.4f} {rmean:>11.4f} "
                  f"{M/rmean:>9.4f} {M/math.sqrt(n):>9.4f} {M/math.sqrt(n*lnm):>14.4f}")
    print()
    print("=" * 78)
    print("(3) PRIZE-PERIOD dilation correlations D(lambda) (HD-doubling = lambda=2)")
    print("=" * 78)
    for n in [8, 16]:
        p = find_prime_cong1(n, 2003)
        dc, m = prize_dilation_corr(p, n)
        # find lambda=2 specifically
        d2 = next((v for v, l in dc if l == 2), None)
        # find lambda = -1 = m-1 (conjugation)
        dm1 = next((v for v, l in dc if l == m - 1), None)
        print(f"  n={n} p={p} m={m}:  HD-doubling D(2) = {d2 if d2 is not None else 'n/a (gcd)'}"
              f"   conjugation D(-1)=D({m-1}) = {dm1 if dm1 is not None else 'n/a'}")
        print(f"     top dilation correlations:")
        for v, l in dc[:5]:
            print(f"        lambda={l:>4}: {v:.4f}")
        print(f"     noise floor ~ 1/sqrt(m) = {1/math.sqrt(m):.4f}")

if __name__ == '__main__':
    run()
