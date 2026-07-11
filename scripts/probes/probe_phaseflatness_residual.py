#!/usr/bin/env python3
"""
TOOL 2 ADVERSARIAL TEST (#444): phase-flatness of arithmetic root-number phases.

Object.  For a prime p, m = p-1 multiplicative characters chi of F_p^*.  The GAUSS-SUM
root numbers are  gamma_chi = G(chi)/sqrt(p)  (unit modulus for chi != chi_0).  The dual
exponential sum over the additive index b in Z/m is
    P(b) = sum_{chi != 1} conj(chi)(b-th power index?) gamma_chi    [we use the cyclic index]
We index characters by j in {1,..,m-1} via a fixed generator g of F_p^*:  chi_j(g^t) = e(jt/m).
Then the natural dual sum at frequency f is
    F(f) = sum_{j=1}^{m-1} gamma_{chi_j} e(-j f / m).
This is a unit-phase exponential sum of length m-1; its sup-norm maxF = max_f |F(f)|.

BASELINE.  "Random-odd": replace gamma_chi by random unit phases (or random +-1-odd phases)
and measure maxF/sqrt(m).  A Steinhaus random unimodular sequence of length L has
E[max_f |F(f)|] ~ sqrt(L log L) (sqrt(L) * sqrt(log L) factor).  We measure the realized ratio
maxF/sqrt(m) for arithmetic phases vs random and report the % improvement.

NEW ANGLE (beyond the dead HD-doubling correlation).  We test a MULTIPLICATIVE-SHIFT structure:
the sequence a_j = gamma_{chi_j} indexed by j in (Z/m)^*-action.  Specifically:
  (1) higher-order autocorrelation  A_t(h) = sum_j a_j conj(a_{j+h}) ... a (t-point) correlation;
  (2) the MULTIPLICATIVE dilation correlation  D(lambda) = sum_j a_j conj(a_{lambda j mod m})
      for lambda in (Z/m)^* (NOT the additive HD-doubling lambda=2 only; ALL dilations).
      If some dilation lambda gives |D(lambda)| ~ m (strong correlation), the phases have
      exploitable multiplicative self-similarity -> a structured (sparse) Fourier transform.
  (3) the QUADRATIC / chi^2 (Hasse-Davenport) shift as a special case lambda=2 to confirm corr~0.

Honesty: report ACTUAL maxF/sqrt(m). If arith beats random by 15-20% it CONFIRMS Tool 2's claim;
if the new dilation correlations are all ~sqrt(m) (noise floor) the residual is DIFFUSE (Tool 2's
'same wall'). A large |D(lambda)| would be a genuine NEW exploitable structure (refutes 'diffuse').
"""
import math, cmath, random

def is_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1
    factors = set()
    n = phi; d = 2
    while d * d <= n:
        if n % d == 0:
            factors.add(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: factors.add(n)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    return None

def gauss_phases(p):
    """gamma_chi_j = G(chi_j)/sqrt(p) for j=1..m-1, m=p-1.  chi_j(g^t)=e(jt/m).
       G(chi_j) = sum_{x=1}^{p-1} chi_j(x) e(x/p) = sum_{t=0}^{m-1} e(j t/m) e(g^t / p)."""
    m = p - 1
    g = primitive_root(p)
    # discrete log table: dlog[x] = t with g^t = x
    dlog = [0] * p
    gp = 1
    for t in range(m):
        dlog[gp] = t
        gp = gp * g % p
    # additive char value e(x/p) indexed by x
    ax = [cmath.exp(2j * math.pi * x / p) for x in range(p)]
    sq = math.sqrt(p)
    gammas = [0j] * m   # index 0 unused (chi_0 trivial), j=1..m-1
    for j in range(1, m):
        s = 0j
        # G(chi_j) = sum_{x=1}^{p-1} e(j*dlog[x]/m) * e(x/p)
        for x in range(1, p):
            s += cmath.exp(2j * math.pi * j * dlog[x] / m) * ax[x]
        gammas[j] = s / sq
    return gammas, m, g

def sup_norm(a, m):
    """maxF = max over frequencies f of |sum_{j=1}^{m-1} a_j e(-j f/m)| (FFT-free, exact-ish)."""
    # length m DFT of the sequence indexed 0..m-1 (a_0 := 0)
    seq = [0j] * m
    for j in range(1, m):
        seq[j] = a[j]
    best = 0.0; argf = 0
    for f in range(m):
        s = sum(seq[j] * cmath.exp(-2j * math.pi * j * f / m) for j in range(m))
        mag = abs(s)
        if mag > best: best = mag; argf = f
    return best, argf

def random_unit_baseline(m, trials, seed=0):
    """E[maxF] for Steinhaus random unimodular a_j (j=1..m-1)."""
    rng = random.Random(seed)
    vals = []
    for _ in range(trials):
        a = [0j] + [cmath.exp(2j * math.pi * rng.random()) for _ in range(m - 1)]
        mx, _ = sup_norm(a, m)
        vals.append(mx)
    return sum(vals) / len(vals), max(vals), min(vals)

def random_odd_baseline(m, trials, seed=0):
    """E[maxF] for random ODD-sign real phases a_j in {+-1} (the 'random-odd' baseline)."""
    rng = random.Random(seed + 99)
    vals = []
    for _ in range(trials):
        a = [0] + [rng.choice([1.0, -1.0]) for _ in range(m - 1)]
        a = [complex(x) for x in a]
        mx, _ = sup_norm(a, m)
        vals.append(mx)
    return sum(vals) / len(vals), max(vals), min(vals)

def dilation_corr(a, m):
    """NEW ANGLE: multiplicative dilation correlation D(lambda)= sum_j a_j conj(a_{(lambda*j) mod m})
       over lambda in (Z/m)^*.  Returns sorted top correlations |D(lambda)|/(m-1).
       HD-doubling = lambda=2 (special case)."""
    res = []
    norm = m - 1
    for lam in range(2, m):
        if math.gcd(lam, m) != 1:
            continue
        s = 0j
        for j in range(1, m):
            jj = (lam * j) % m
            if jj == 0:  # shouldn't happen for gcd=1, j in 1..m-1
                continue
            s += a[j] * a[jj].conjugate()
        res.append((abs(s) / norm, lam))
    res.sort(reverse=True)
    return res

def autocorr_additive(a, m, t=2):
    """Additive higher-order autocorr A_t(h)=sum_j prod ... ; here t=2: standard a_j conj a_{j+h}.
       Report max over h!=0 of |A_2(h)|/(m-1) (should be ~1/sqrt(m) for flat)."""
    norm = m - 1
    best = 0.0; argh = 0
    for h in range(1, m):
        s = sum(a[j] * a[(j + h) % m if (j + h) % m != 0 else 0].conjugate()
                for j in range(1, m) if (j + h) % m != 0)
        if abs(s) / norm > best:
            best = abs(s) / norm; argh = h
    return best, argh

def run(p):
    print("=" * 78)
    print(f"PHASE-FLATNESS at p={p}, m={p-1} (Gauss-sum root-number phases)")
    print("=" * 78)
    gammas, m, g = gauss_phases(p)
    # sanity: |gamma_chi| should be 1
    mags = [abs(gammas[j]) for j in range(1, m)]
    print(f"  |gamma_chi| range: [{min(mags):.4f}, {max(mags):.4f}] (should be 1.0)")
    # arithmetic sup-norm
    maxF_arith, argf = sup_norm(gammas, m)
    rt = math.sqrt(m)
    print(f"  ARITH  maxF = {maxF_arith:.4f}   maxF/sqrt(m) = {maxF_arith/rt:.4f}  (at f={argf})")
    # baselines
    trials = 40 if m < 500 else 12
    ru_mean, ru_max, ru_min = random_unit_baseline(m, trials)
    ro_mean, ro_max, ro_min = random_odd_baseline(m, trials)
    print(f"  RAND-UNIT (Steinhaus) E[maxF]/sqrt(m) = {ru_mean/rt:.4f}  "
          f"[min {ru_min/rt:.4f}, max {ru_max/rt:.4f}], {trials} trials")
    print(f"  RAND-ODD  (+-1)       E[maxF]/sqrt(m) = {ro_mean/rt:.4f}  "
          f"[min {ro_min/rt:.4f}, max {ro_max/rt:.4f}], {trials} trials")
    impr_u = 100 * (ru_mean - maxF_arith) / ru_mean
    impr_o = 100 * (ro_mean - maxF_arith) / ro_mean
    print(f"  => ARITH beats RAND-UNIT by {impr_u:+.1f}%,  beats RAND-ODD by {impr_o:+.1f}%")
    # NEW ANGLE 1: multiplicative dilation correlations (all lambda, incl HD lambda=2)
    dc = dilation_corr(gammas, m)
    print(f"  [NEW] top multiplicative-dilation correlations |D(lambda)|/(m-1):")
    for val, lam in dc[:6]:
        tag = "  <-- HD-doubling" if lam == 2 else ""
        print(f"        lambda={lam:>4}: {val:.4f}{tag}")
    noise = 1.0 / math.sqrt(m)
    print(f"        (flat/noise floor ~ 1/sqrt(m) = {noise:.4f}; "
          f"a value ~1.0 = strong exploitable structure)")
    # NEW ANGLE 2: additive 2-pt autocorrelation max
    ac, argh = autocorr_additive(gammas, m, t=2)
    print(f"  [NEW] max additive autocorr |A_2(h)|/(m-1) over h!=0 = {ac:.4f} (at h={argh}); "
          f"noise ~ {noise:.4f}")
    return maxF_arith / rt, impr_u, impr_o, dc[0] if dc else (0, 0), ac

if __name__ == '__main__':
    results = []
    # several primes; keep m=p-1 modest so the m x m DFT + dilation scan is tractable
    for p in [101, 211, 401, 601, 1009]:
        if is_prime(p):
            r = run(p)
            results.append((p, r))
    print("=" * 78)
    print("SUMMARY  p | maxF/sqrt(m) arith | vs rand-unit | vs rand-odd | top dilation corr | max autocorr")
    for p, (ratio, iu, io, (dval, dlam), ac) in results:
        print(f"  {p:>5} |   {ratio:.4f}          | {iu:+5.1f}%      | {io:+5.1f}%     | "
              f"{dval:.4f}(lam{dlam}) | {ac:.4f}")
