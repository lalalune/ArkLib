#!/usr/bin/env python3
"""
Door-(iv) Lane-1 probe (#464) — GAP-SEQUENCE circular AUTOCORRELATION / SPECTRAL RANK
of the worst-b coset of the thin 2-power subgroup mu_n < F_p^*.

GENUINELY-NEW object (deconflicted vs mapped faces):
  - gap VALUES collapse to <= n/2+1 (ThreeGapPositionalRigidity, dilation-invariant)  [DEAD]
  - 2nd-difference (curvature) complexity is MAXIMAL = n, dilation-invariant            [DEAD, a670238d0]
  NOT measured: the *circular autocorrelation spectrum* of the GAP sequence g_i itself.
  If the gap sequence has a LOW-RANK circular structure (few nonzero DFT coefficients =
  quasi-periodic), that is a SPECTRAL lever distinct from value-count and curvature, and
  it does NOT route through multiplicative energy. A low-rank gap spectrum could in
  principle be gripped by a structured small-ball bound.

THE QUESTION (frequency-SENSITIVE => passes rule-3 only if it DIFFERS at b* vs generic b):
  Q1. #significant DFT modes of the gap sequence g_i (i=0..n-1) at the worst b*.
      Full-rank ~ n nonzero modes (generic, no structure); low-rank ~ O(1) (exploitable).
  Q2. Is the mode-count at b* DIFFERENT from a generic non-worst b? If identical => DEAD.
  Q3. Does it grow with thinness n or stay O(1)?

Prize regime: PROPER mu_n < F_p^*, p == 1 mod n, p ~ n^4 >> n^3, NEVER n=q-1.
UNIFORM coset-rep sampling (no scan-stride artifact). EXACT integer gaps; float DFT only
for spectral rank (a magnitude statistic). Multiple structured primes; median. Empirical only.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, beta, count):
    target = n**beta
    lo = max(target//2, n**3 + 1)
    out = []
    k = (lo-1)//n + 1
    while len(out) < count and k < 50_000_000:
        p = 1 + k*n
        if p > lo and is_prime(p):
            out.append(p)
        k += 1
    return out

def subgroup_mu_n(p, n):
    m = p-1
    fac = set(); mm = m; d = 2
    while d*d <= mm:
        while mm % d == 0: fac.add(d); mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    g = None
    for cand in range(2, p):
        if all(pow(cand, m//q, p) != 1 for q in fac):
            g = cand; break
    h = pow(g, (p-1)//n, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*h) % p
    return mu

def eta_abs2(b, mu, p):
    s = 0j
    for x in mu:
        ang = 2*math.pi*((b*x) % p)/p
        s += cmath.exp(1j*ang)
    return s.real*s.real + s.imag*s.imag

def gap_sequence(b, mu, p):
    pos = sorted(((b*x) % p) for x in mu)
    N = len(pos)
    return [(pos[(i+1) % N] - pos[i]) % p for i in range(N)]

def spectral_rank(seq, rel_tol=0.02):
    """#DFT modes (excluding the DC mode) with magnitude >= rel_tol * max-nonDC-magnitude.
    Mean-centered so DC (mode 0) is dropped; counts the 'significant' AC structure."""
    N = len(seq)
    mean = sum(seq)/N
    c = [v - mean for v in seq]
    mags = []
    for k in range(1, N):  # skip DC
        s = sum(c[j]*cmath.exp(-2j*math.pi*k*j/N) for j in range(N))
        mags.append(abs(s))
    if not mags:
        return 0
    mx = max(mags)
    if mx == 0:
        return 0
    return sum(1 for v in mags if v >= rel_tol*mx)

def main():
    print("# Door-IV worst-b GAP-SEQUENCE autocorrelation/spectral-RANK probe (#464)")
    print("# columns: n  p  worstb  specRank(b*)  | generic specRank   (full ~ n-1)")
    import statistics as st
    for n in [16, 32, 64]:
        ps = primes_1_mod_n(n, 4, 4)
        if not ps:
            print(f"# n={n}: no primes"); continue
        rs_star, rs_gen = [], []
        for p in ps:
            mu = subgroup_mu_n(p, n)
            random.seed(464 + p)
            m = (p-1)//n
            seen = {}; cands = []; tries = 0
            while len(cands) < min(300, m) and tries < 3000:
                b = random.randrange(1, p)
                cmin = min((b*x) % p for x in mu)
                if cmin not in seen:
                    seen[cmin] = b; cands.append(b)
                tries += 1
            bstar = max(cands, key=lambda b: eta_abs2(b, mu, p))
            rstar = spectral_rank(gap_sequence(bstar, mu, p))
            genb = random.choice([b for b in cands if b != bstar]) if len(cands) > 1 else bstar
            rgen = spectral_rank(gap_sequence(genb, mu, p))
            rs_star.append(rstar); rs_gen.append(rgen)
            print(f"  n={n:3d}  p={p:>10d}  b*={bstar:>9d}  specRank*={rstar:>3d}  | gen={rgen:>3d}")
        ms = st.median(rs_star); mg = st.median(rs_gen)
        verdict = "YES (frequency-sensitive — LIVE)" if ms != mg else "NO (dilation-invariant => DEAD)"
        print(f"# n={n}: median specRank(b*)={ms}  generic={mg}  (full = {n-1})  frequency-sensitive? {verdict}")
    print("# DONE")

if __name__ == "__main__":
    main()
