#!/usr/bin/env python3
"""
THE OPEN ≥2-D QUESTION (#444, opened in comment 2026-06-15T14:14:50Z):
RealizerL2NotSup proved the 1-D far-line incidence is B-BLIND (annihilator {b:b·s1=0}={0}
over a field => only the principal eta_0=|G| survives, p-INDEPENDENT). The decisive open
question: does the >=2-D incidence (annihilator a NONTRIVIAL frequency-subspace) re-couple
to the sup B = max_{b!=0}||eta_b|| (=> wall stays), or is it STILL L2/average-measurable
(=> delta* is COMPUTABLE, prize reframed)?

EXACT 2-D MODEL. Syndrome space V = F^2. A direction s1 in F^2, s1 != 0, has annihilator
  Ann(s1) = { b in F^2 : b . s1 = 0 }  =  a 1-D F_p-subspace = { t * b0 : t in F_p }, |Ann| = p.
The 2-D incidence-period identity (term-by-term Fourier inversion, same derivation as
lineIncidence_period_sum but over F^2) is
  I_2(s0, s1) = sum_{b in Ann(s1)} conj(Eta(b)) * psi(b . s0)
where Eta(b) for b=(b1,b2) in F^2 is the period of the 2-D ball. We take the prize-relevant
ball G = mu_n lifted to a CURVE/graph {(x, x^j) : x in mu_n} (a degree-j monomial graph,
the natural 2-D lift that the MCA witness sets live on). Then
  Eta(b1,b2) = sum_{x in mu_n} e_p(b1*x + b2*x^j) = a TWISTED character sum over mu_n.

So the surviving frequencies along a line Ann(s1)={t*b0} contribute
  sum_{t in F_p} conj(Eta(t*b0)) * psi(t * (b0.s0))
i.e. a sum over a GEOMETRIC FAMILY of twisted periods. The MAX over (s0,s1) of |I_2| is the
2-D incidence object. QUESTION: is max|I_2| p-INDEPENDENT (L2/avg-blind, like 1-D) or
p-DEPENDENT (sees B)?

DECISIVE TEST (same logic as probe_realizer_supVSavg / farLine_incidence: a functional that
stays fixed while B varies over p CANNOT be an increasing function of B):
  - compute B = max_{b!=0} ||eta_b|| (1-D subgroup period sup) for several primes p = 1 mod n
  - compute MAXI2 = max over directions of |I_2| for the SAME primes
  - if B varies strongly across p but MAXI2 stays fixed => 2-D incidence ALSO B-blind (computable).
  - if MAXI2 tracks B (both move together) => the 2-D incidence RE-COUPLES to the wall.

We also report MAXI2 / (the L2-average scale) and MAXI2 / B to see which it tracks.
PROBE-FIRST DISCIPLINE: PROPER mu_n (n=2^a, n | p-1), p >> n^3, multiple primes incl structured,
NEVER n=q-1.
"""
import cmath, math, itertools, sys
import numpy as np

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5)+1):
        if m % d == 0: return False
    return True

def primes_cong1(n, lo, count, structured=False):
    out = []
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while len(out) < count:
        if p > 2 and p % n == 1 and is_prime(p):
            out.append(p)
        p += n
    return out

def subgroup(n, p):
    # find generator g of F_p*, return mu_n = {g^{(p-1)/n * j}}
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = x*a % p; o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p-1:
            g = cand; break
    h = pow(g, (p-1)//n, p)   # primitive n-th root
    return [pow(h, j, p) for j in range(n)]

def ep(p):
    w = 2j*math.pi/p
    return lambda t: cmath.exp(w * (t % p))

def sup_B_1d(mu, p):
    """B = max_{b!=0} | sum_{x in mu} e_p(b x) |  (the 1-D subgroup sup -- the open wall)."""
    e = ep(p)
    B = 0.0; argmax = None
    for b in range(1, p):
        s = sum(e(b*x) for x in mu)
        m = abs(s)
        if m > B: B = m; argmax = b
    return B, argmax

def eta2(mu, p, b1, b2, j, e):
    """2-D twisted period on the monomial graph {(x, x^j)}: sum_{x in mu} e_p(b1 x + b2 x^j)."""
    return sum(e(b1*x + b2*pow(x, j, p)) for x in mu)

def max_I2(mu, p, j, e, sample_dirs=None):
    """
    max over directions s1!=0 in F^2 of |I_2(s0,s1)| = | sum_{b in Ann(s1)} conj(eta2(b)) psi(b.s0) |.
    Ann(s1) for s1=(a,c) is the line { t*(c,-a) : t in F_p } (perp in F^2). Enumerate primitive
    directions b0=(c,-a) up to scale (projective line P^1(F_p): p+1 points). For each b0, the
    incidence at offset s0 is sum_t conj(eta2(t*b0)) psi(t*(b0.s0)); we maximize |.| over the
    'frequency' u := (b0.s0) which ranges over all of F_p as s0 varies => it's a 1-D DFT of the
    sequence c_t = conj(eta2(t*b0)) over t, and max_u |sum_t c_t psi(t u)| is its sup-DFT (FFT).

    VECTORIZED. Precompute eta2(w1,w2) for ALL w=(w1,w2) is O(p^2 * n); instead note that along
    direction b0 we need eta2(t*b0) for t in F_p. eta2(b1,b2)=sum_x e_p(b1 x + b2 x^j). Precompute
    for each x in mu the pair (x, x^j); then eta2(t*b01,t*b02)=sum_x e_p(t*(b01 x + b02 x^j))
    = sum_x w^{ t * phi_x }  where phi_x = (b01*x + b02*x^j) mod p, w = e_p(1). So along the line,
    c_t = conj( sum_x w^{ t*phi_x } ). The DFT over t (length p) is then done by numpy FFT.
    """
    mu = np.array(mu, dtype=np.int64)
    xj = np.array([pow(int(x), j, p) for x in mu], dtype=np.int64)
    w = np.exp(2j*np.pi/p)
    dirs = [(1, m) for m in range(p)] + [(0, 1)]
    tvec = np.arange(p)
    best = 0.0; bestinfo = None
    for (b01, b02) in dirs:
        phi = (b01*mu + b02*xj) % p           # per-x phase coefficient, shape (n,)
        # c_t = conj( sum_x exp(2pi i * (t*phi_x)/p) ), t=0..p-1
        # build matrix exp via outer product t*phi mod p
        M = np.outer(tvec, phi) % p           # (p, n)
        eta = np.exp(2j*np.pi*M/p).sum(axis=1)  # (p,) = sum_x w^{t phi_x}
        c = np.conjugate(eta)
        # sup over u of |FFT(c)|; numpy fft uses e^{-2pi i t u/p}; magnitude is direction-agnostic
        C = np.fft.fft(c)
        m = np.abs(C)
        idx = int(np.argmax(m))
        if m[idx] > best:
            best = float(m[idx]); bestinfo = (b01, b02, idx)
    return best, bestinfo

def main():
    # prize-shaped but COMPUTABLE: n=2^a small, p >> n^3, j = a monomial-graph degree (use small)
    for n in [4, 8]:
        for j in [2, 3]:
            lo = max(n**3, 200)
            primes = primes_cong1(n, lo, 4)
            print(f"\n==== n={n} (mu_n PROPER, n|p-1, p>>n^3), monomial-graph degree j={j} ====")
            print(f"{'p':>8} {'B(1d sup)':>10} {'maxI2(2d)':>10} {'sqrt(n)':>8} "
                  f"{'maxI2/B':>8} {'maxI2/n':>8} {'maxI2/sqrt(n)':>13}")
            rows = []
            for p in primes:
                mu = subgroup(n, p)
                e = ep(p)
                B, _ = sup_B_1d(mu, p)
                I2, info = max_I2(mu, p, j, e)
                rows.append((p, B, I2))
                print(f"{p:>8} {B:>10.4f} {I2:>10.4f} {math.sqrt(n):>8.3f} "
                      f"{I2/B:>8.4f} {I2/n:>8.4f} {I2/math.sqrt(n):>13.4f}")
            # verdict: does maxI2 vary with p (track B) or stay fixed (L2-blind)?
            Bs = [r[1] for r in rows]; I2s = [r[2] for r in rows]
            Bspread = (max(Bs)-min(Bs))/ (sum(Bs)/len(Bs))
            I2spread = (max(I2s)-min(I2s)) / (sum(I2s)/len(I2s))
            print(f"  -> B rel-spread across p = {Bspread:.4f} ; maxI2 rel-spread = {I2spread:.4f}")
            if I2spread < 0.02 and Bspread > 0.05:
                print("  => VERDICT: maxI2 is p-INDEPENDENT while B varies => 2-D incidence is "
                      "ALSO B-BLIND (L2/average-measurable). delta* COMPUTABLE on this graph.")
            elif I2spread > 0.5*Bspread:
                print("  => VERDICT: maxI2 TRACKS B (both p-dependent) => 2-D incidence RE-COUPLES "
                      "to the sup wall.")
            else:
                print("  => VERDICT: ambiguous (partial coupling) -- inspect ratios.")

if __name__ == "__main__":
    main()
