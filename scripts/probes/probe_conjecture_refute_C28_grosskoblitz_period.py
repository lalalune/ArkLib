#!/usr/bin/env python3
"""C28 ATTACK (#444): Gross-Koblitz p-adic Gamma evaluation of the period argument.

CONJECTURE C28: Use Gross-Koblitz  tau(chi) = -pi^{s(chi)} prod Gamma_p(<...>) to evaluate
the period eta_c exactly as an algebraic integer; claim the EXPLICIT p-adic Gamma factors pin
the complex arguments arg tau(chi_j) tightly enough to force max_c|eta_c| <= C*sqrt(n log p)
PAST Johnson. "An exact evaluation, not an estimate."

WHAT GROSS-KOBLITZ ACTUALLY GIVES (the load-bearing facts):
 (GK1) GK is a p-ADIC identity. It expresses tau(chi) in the p-adic completion C_p via the
       Morita p-adic Gamma function Gamma_p. It pins the p-adic valuation v_p(tau(chi)) (=
       Stickelberger / s(chi)/(p-1)) and the p-adic UNIT. It does NOT directly give the
       ARCHIMEDEAN (complex) argument arg tau(chi) in C, which is what the floor max_c|eta_c|
       (a sum of COMPLEX magnitudes) depends on. The archimedean |tau(chi)| = sqrt(q) is the
       Weil/Gauss-sum magnitude, char-INDEPENDENT, already known. GK adds the p-adic phase.
 (GK2) The floor is  eta_b = (1/f) sum_j conj(chi^j(b)) tau(chi^j)  with each |tau|=sqrt(q),
       so max_b|eta_b| is the SUP over b of a DFT of the f Gauss-sum vectors. This sup is
       governed by the JOINT ARCHIMEDEAN PHASE distribution {arg tau(chi^j)}_j and the maximal
       coherence over b.

THE DECISIVE QUESTION (the horn-finder):
   Does GK constrain arg tau(chi^j) MORE than equidistribution? If the floor B = max_b|eta_b|
   is statistically INDISTINGUISHABLE from the random-phase prediction (the f Gauss sums act
   as random vectors of length sqrt(q)), then GK pins NO archimedean coherence -> the sup is
   exactly the BGK joint-pseudorandomness wall -> C28 SECRETLY-OPEN.
   If GK forced extra archimedean rigidity, B would be SYSTEMATICALLY BELOW the random null.

PROBE: proper subgroup mu_n (n=2^mu), p PRIME, p >> n^3 (NEVER n=p-1).
 (T1) Verify the Gauss-period decomposition reproduces eta_b (sanity).
 (T2) Compare actual floor B vs random-phase null (f Gauss sums -> random phases, same DFT).
      Report percentile of B in the null. Random-like => B sits mid-distribution, NOT below.
 (T3) Direct test of the GK claim: does GK's archimedean phase structure beat random?
      Measure the GAP statistic  (null_median - B)/null_std : negative or ~0 => no rigidity.
"""
import math, cmath, random
import numpy as np

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primroot(p):
    fac = set(); m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for a in range(2, p):
        if all(pow(a, (p-1)//q, p) != 1 for q in fac): return a

def analyze(n, p, seed=12345, ntrials=300):
    """Return (B, null_pctile, gap_in_sigma, recon_err) for mu_n in F_p."""
    g0 = primroot(p)
    f = (p-1)//n                       # m = index = number of distinct eta values
    # discrete log
    dlog = [0]*p; cur = 1
    for t in range(p-1):
        dlog[cur] = t; cur = cur*g0 % p
    # mu_n = <g0^f>
    g = pow(g0, f, p)
    H = [pow(g, i, p) for i in range(n)]
    tp = 2*math.pi
    ep = np.exp(2j*np.pi*np.arange(p)/p)
    # Gauss sums tau(chi^s) for ALL s=0..f-1 at once.
    # chi_s(x) = exp(2pi i n s dlog(x)/(p-1)).  tau_s = sum_{x=1}^{p-1} chi_s(x) e_p(x).
    # Group e_p(x) contributions by dlog(x): w[d] = e_p(g0^d) (d=0..p-2). Then
    #   tau_s = sum_{d=0}^{p-2} exp(2pi i n s d/(p-1)) w[d]  = FFT-like over d with step n s.
    dl = np.empty(p-1, dtype=np.int64)  # not needed; build w directly
    w = np.empty(p-1, dtype=complex)
    xcur = 1
    for d in range(p-1):
        w[d] = ep[xcur]
        xcur = xcur*g0 % p
    darr = np.arange(p-1)
    Gs = np.empty(f, dtype=complex)
    for s in range(f):
        Gs[s] = np.sum(np.exp(2j*np.pi*(n*s % (p-1))*darr/(p-1))*w)
    # eta_b directly over coset reps b=g0^c
    etas = np.empty(f, dtype=complex)
    Harr = np.array(H, dtype=np.int64)
    b = 1
    for c in range(f):
        etas[c] = np.sum(ep[(b*Harr) % p])
        b = b*g0 % p
    # reconstruct: eta_{g0^c} = (1/f) sum_s exp(-2pi i n s c/(p-1)) tau_s.
    # dlog(g0^c)=c, so chi_s(g0^c)=exp(2pi i n s c/(p-1)); conj gives the minus sign. n c/(p-1)=c/f.
    recon = np.fft.fft(Gs)/f   # sum_s exp(-2pi i c s/f) Gs[s], c=0..f-1
    recon_err = float(np.max(np.abs(etas - recon)))
    B = float(np.max(np.abs(etas)))
    # NULL: keep |tau|=sqrt(p) for s!=0, tau_0=-1; randomize archimedean phases; same DFT sup.
    # eta_c (over coset reps b=g0^c) = (1/f) sum_s exp(-2pi i c s / f) tau_s  =  ifft(tau)*...
    # i.e. the DFT sup is computed via FFT for speed.  (np.fft.fft(rt) gives sum_s rt[s] exp(-2pi i c s/f).)
    rng = random.Random(seed)
    sq = math.sqrt(p)
    nulls = []
    G0 = Gs[0]
    for _ in range(ntrials):
        ph = np.array([rng.random() for _ in range(f-1)])
        rt = np.empty(f, dtype=complex)
        rt[0] = G0
        rt[1:] = sq*np.exp(2j*np.pi*ph)
        vals = np.fft.fft(rt)/f
        nulls.append(float(np.max(np.abs(vals))))
    nulls.sort()
    below = sum(1 for x in nulls if x < B)
    pctile = below/len(nulls)
    mean = sum(nulls)/len(nulls)
    var = sum((x-mean)**2 for x in nulls)/len(nulls)
    sd = math.sqrt(var) if var > 0 else 1e-12
    # gap_in_sigma>0 means B BELOW null mean (=GK rigidity); <=0 means B at/above (=no rigidity)
    gap_in_sigma = (mean - B)/sd
    return B, pctile, gap_in_sigma, recon_err, f, mean, sd

if __name__ == "__main__":
    print("=== C28: Gross-Koblitz archimedean-phase rigidity test for the floor max_b|eta_b| ===")
    print("p PRIME, mu_n proper 2-power subgroup, p >> n^3, NEVER n=p-1.")
    print("If GK forced sub-random coherence, B would be BELOW null (gap_sigma >> 0).")
    print()
    print(f"{'n':>4} {'p':>7} {'f':>5} {'p/n^3':>7} {'B':>9} {'B/sqrtn':>8} {'null_mean':>10} {'pctile':>7} {'gap_sigma':>9} {'reconerr':>9}")
    cases = [
        (16, None), (16, None), (16, None),
        (32, None), (32, None),
        (64, None),
    ]
    # pick primes p>>n^3 with n | p-1
    # (n, target_p, want, ntrials). p>>n^3 (margin>=2x), p prime, n|p-1, never n=p-1. Compute~p^2/n.
    plans = [
        (8,  3*8**3,  3, 400),    # n^3=512,  p~1536
        (8,  20*8**3, 2, 400),    # bigger margin to confirm robustness
        (16, 3*16**3, 3, 300),    # n^3=4096, p~12288
        (32, 2*32**3, 2, 200),    # n^3=32768,p~65536  (p^2/n ~ 1.3e8, ok)
    ]
    for n, target, want, ntr in plans:
        found = 0
        p0 = target - (target % n) + 1
        d = 0
        while found < want and d < 200*n:
            pp = p0 + d
            if pp > n and isprime(pp) and (pp-1) % n == 0 and (pp-1) != n:
                B, pct, gs, re, f, mean, sd = analyze(n, pp, ntrials=ntr)
                print(f"{n:>4} {pp:>7} {f:>5} {pp/n**3:>7.2f} {B:>9.2f} {B/math.sqrt(n):>8.3f} {mean:>10.2f} {pct:>7.2f} {gs:>9.2f} {re:>9.1e}")
                found += 1
            d += n
    print()
    print("VERDICT KEY: pctile in (0,1) and gap_sigma ~ 0 (not >>0) => GK adds NO archimedean")
    print("rigidity to the floor; B = random-phase value = BGK joint-pseudorandomness wall.")
