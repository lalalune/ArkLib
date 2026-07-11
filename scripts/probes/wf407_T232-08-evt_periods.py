"""
wf407 / T232-08-evt : worst-period EVT scaling B ~ sqrt(n log m) for the
exchangeable Gauss-period family.

Exact (NOT sampled) computation over real prime fields F_p, subgroup G = mu_n
(the order-n multiplicative subgroup), additive character psi(x) = exp(2*pi*i*x/p).

Quantities (b ranges over F_p^*, but eta is constant on the m = (p-1)/n cosets
of G in F_p^*, so there are exactly m distinct *period* values eta_c).

  eta_c = sum_{y in G} psi(g_rep_c * y)        (c = 0..m-1, one rep per coset)
  Re-part / Im-part are the real coords.
  X_c = |eta_c|^2  (the "energy" of period c)  -- the object whose MAX is B^2.

We test, EXACTLY:
  (A) Exchangeability fingerprint of the *complex* periods:
        sum_c eta_c = -1   (since sum over ALL b incl 0 is 0; eta_0 = n)
        -> sum_{c} eta_c = -1, i.e. mean(eta_c) = -1/m  (the ONE linear constraint).
        sum_c |eta_c|^2 = (p*n - n^2)/n = p - n   (peel trivial term), so
        Var(|eta|... ) etc.  We check Cov structure of the REAL parts:
        Cov(Re eta_c, Re eta_{c'}) for c != c' should equal -Var/(m-1).
  (B) The plateau C = B / sqrt(n * ln m), B = max_c |eta_c|.
  (C) EVT test: compare B^2 = max_c |eta_c|^2 to the i.i.d.-Gaussian prediction.
        For m i.i.d. complex Gaussians with E|eta|^2 = n (each real coord var n/2),
        |eta|^2 ~ (n/2)*ChiSq(2) = n * Exp(1); max of m i.i.d. Exp(1) ~ ln m + gamma.
        => predicted B^2_iid ~ n * ln m  => B_iid ~ sqrt(n ln m), C_iid -> 1.
        ALSO directional Gumbel: max_c Re(eta_c) ~ sqrt(2 * (n/2) * ln m) = sqrt(n ln m).
        We report ratio R_energy = B^2 / (n ln m), and the directional analogue.
"""
import numpy as np
from math import gcd, log, sqrt, pi

def primitive_root(p):
    # find a generator of F_p^*
    if p == 2:
        return 1
    phi = p - 1
    # factor phi
    fac = []
    x = phi
    d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def periods(p, n):
    """Return the m distinct complex Gauss-period values eta_c, exact via numpy complex128."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    # subgroup G = <g^m> has order n. Elements: g^{m*j}, j=0..n-1
    gm = pow(g, m, p)
    G = []
    cur = 1
    for _ in range(n):
        G.append(cur)
        cur = (cur * gm) % p
    G = np.array(G, dtype=np.int64)
    # coset reps: g^c, c=0..m-1 multiply G; eta_c = sum_{y in G} psi(g^c * y)
    w = 2.0 * pi / p
    etas = np.empty(m, dtype=np.complex128)
    gc = 1
    for c in range(m):
        # arguments: gc * G mod p
        args = (gc * G) % p
        etas[c] = np.sum(np.exp(1j * w * args))
        gc = (gc * g) % p
    return etas, m

def analyze(p, n):
    etas, m = periods(p, n)
    re = etas.real
    im = etas.imag
    energy = np.abs(etas) ** 2
    B2 = energy.max()
    B = sqrt(B2)
    lnm = log(m) if m > 1 else 0.0
    # constraint check
    sum_eta = etas.sum()
    sum_energy = energy.sum()
    # exchangeability: Cov(Re_c, Re_c') for c!=c' should be -Var/(m-1)
    mu_re = re.mean()
    var_re = re.var()            # population variance (1/m)
    # total cross-cov: (sum re)^2 = sum re^2 + sum_{c!=c'} re_c re_c'
    S = re.sum()
    cross = (S * S - (re * re).sum()) / (m * (m - 1)) - mu_re * mu_re  # avg Cov over c!=c'
    # the exchangeable prediction: Cov_offdiag = -var_re/(m-1)   (so that row sums of cov ~ 0)
    pred_cov = -var_re / (m - 1)
    C = B / sqrt(n * lnm) if lnm > 0 else float('nan')
    R_energy = B2 / (n * lnm) if lnm > 0 else float('nan')
    # directional: max over c of Re(eta_c) (worst real projection)
    maxRe = re.max()
    R_dir = maxRe / sqrt(n * lnm) if lnm > 0 else float('nan')
    return dict(p=p, n=n, m=m, lnm=lnm, B=B, B2=B2, C=C, R_energy=R_energy,
                sum_eta=sum_eta, sum_energy=sum_energy, expect_sum_energy=p - n,
                cross_cov=cross, pred_cov=pred_cov, cov_ratio=(cross / pred_cov if pred_cov != 0 else float('nan')),
                maxRe=maxRe, R_dir=R_dir, var_re=var_re)

# Primes with various m=(p-1)/n; exclude Fermat traps (odd_part(m)>1). n in {8,16,32,64}.
# pick primes p = k*n + 1 prime, with growing m at fixed n to test the plateau / EVT scaling.
def gen_primes_for_n(n, count, start_k=2):
    from sympy import isprime  # try sympy; fallback below
    res = []
    k = start_k
    while len(res) < count:
        p = k * n + 1
        if isprime(p):
            m = (p - 1) // n
            # exclude pure 2-power m (Fermat trap): require odd part of m > 1
            mm = m
            while mm % 2 == 0:
                mm //= 2
            if mm > 1 and p > n * n:  # ensure deep-ish (p > n^2) and not Fermat
                res.append(p)
        k += 1
    return res

if __name__ == "__main__":
    try:
        from sympy import isprime
        HAVE_SYMPY = True
    except Exception:
        HAVE_SYMPY = False

    if not HAVE_SYMPY:
        # simple Miller-Rabin
        def isprime(x):
            if x < 2: return False
            for q in (2,3,5,7,11,13,17,19,23,29,31,37):
                if x % q == 0:
                    return x == q
            d = x - 1; r = 0
            while d % 2 == 0:
                d //= 2; r += 1
            for a in (2,3,5,7,11,13,17,19,23,29,31,37):
                v = pow(a, d, x)
                if v in (1, x - 1): continue
                for _ in range(r - 1):
                    v = v * v % x
                    if v == x - 1: break
                else:
                    return False
            return True
        def gen_primes_for_n(n, count, start_k=2):
            res = []; k = start_k
            while len(res) < count:
                p = k * n + 1
                if isprime(p):
                    m = (p-1)//n; mm = m
                    while mm % 2 == 0: mm //= 2
                    if mm > 1 and p > n*n:
                        res.append(p)
                k += 1
            return res

    print("=== (A) exchangeability + (B) plateau + (C) EVT ratio ===")
    print(f"{'n':>4} {'p':>9} {'m':>7} {'lnm':>6} {'B':>8} {'C=B/sqrt(n lnm)':>16} "
          f"{'R_en=B^2/(n lnm)':>17} {'cov_ratio':>10} {'sumEcheck':>10} {'R_dir':>7}")
    for n in (8, 16, 32, 64):
        ps = gen_primes_for_n(n, 6)
        for p in ps:
            r = analyze(p, n)
            sumE_ok = abs(r['sum_energy'] - r['expect_sum_energy']) < 1e-6
            print(f"{n:>4} {p:>9} {r['m']:>7} {r['lnm']:>6.2f} {r['B']:>8.3f} "
                  f"{r['C']:>16.3f} {r['R_energy']:>17.3f} {r['cov_ratio']:>10.4f} "
                  f"{str(sumE_ok):>10} {r['R_dir']:>7.3f}")
    print()
    print("Notes:")
    print(" * cov_ratio = measured off-diag Cov(Re) / [-Var(Re)/(m-1)]; ~1.0 confirms exchangeable white-noise.")
    print(" * R_dir = max_c Re(eta_c) / sqrt(n ln m); i.i.d.-Gumbel predicts -> 1 (since Var(Re)~n/2, max~sqrt(2*(n/2)*ln m)=sqrt(n ln m)).")
    print(" * R_energy = B^2/(n ln m); i.i.d. complex-Gaussian predicts -> 1.")
    print(" * sumEcheck True confirms sum_c|eta_c|^2 = p - n EXACTLY (the Var constraint).")
