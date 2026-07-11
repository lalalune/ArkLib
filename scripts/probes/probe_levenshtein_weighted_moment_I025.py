#!/usr/bin/env python3
"""
I025 — Levenshtein weighted higher-moment bound on the cyclotomic correlation family.
Attack on M(mu_n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x).

CLAIM under test (the NEW LEMMA): there exists a probability weight w (a positive
combination of additive characters off mu_n) and a constant C with
    M^{2k} <= (1/w_min) * [ k-th WEIGHTED moment - Welch floor ],
the optimal w making the bracket O((n log m)^k) — i.e. the weight "over-weights the worst
frequencies" and breaks the phase-blindness that traps the UNWEIGHTED moment at the Parseval
floor sqrt(n) (per probe_407_moment_order_ceiling.py, (E|eta|^2r)^(1/2r) crawls to the sup).

HONESTY: proper subgroup mu_n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1.

This probe asks three DECISIVE questions:
  (Q1) DIRECTION: Welch/Levenshtein give a LOWER bound on the max-coherence of a family.
       For an UPPER bound on the SPECIFIC family mu_n we need the reverse. Test whether ANY
       nonneg weight w on the frequency index b can produce a *valid upper bound* of the
       form M^{2k} <= (1/w_min)*(weighted moment - floor). i.e. is the bracket even >= w_min*M^{2k}?
  (Q2) Even granting a valid weighted-moment upper bound, can a weight that we are ALLOWED to
       choose (must be computable WITHOUT knowing the answer, e.g. supported off mu_n, a positive
       additive-character combination) make the bracket O((n log m)^k)? Measure the best achievable
       (weighted-moment)^{1/k} / sqrt(n) over a family of natural weights and compare to the
       unweighted power-mean ceiling.
  (Q3) The honest crux: a weight that over-weights the *worst frequency* requires KNOWING the
       worst frequency. Test whether the optimal Levenshtein weight (the one minimizing the bound)
       can be expressed as a low-complexity positive combination of additive chars OFF mu_n
       (the only weights the lemma permits) and whether the resulting bound beats exponent 1-o(1).
"""
import numpy as np
import sympy

def is_prime(m): return sympy.isprime(m)

def find_prime(n, lo):
    # smallest prime p > lo with p == 1 mod n  (proper subgroup; p >> n^3 caller's job)
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p):
            return p
        p += 1

def subgroup_and_etas(p, n):
    g0 = sympy.primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    mu = [pow(g, i, p) for i in range(n)]
    assert len(set(mu)) == n and all(pow(x, n, p) == 1 for x in mu)
    # eta_b for all b in F_p (b=0 is principal = n; exclude for M)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    # eta_b = sum_x w[(b*x) mod p]
    etas = np.zeros(p, dtype=complex)
    muarr = np.array(mu)
    for b in range(p):
        idx = (b * muarr) % p
        etas[b] = w[idx].sum()
    return mu, etas

def main():
    print("=== I025: Levenshtein weighted higher-moment, mu_n = 2-power subgroup ===\n")
    cases = [(8, 8**3 + 50), (16, 16**3 + 50), (32, 32**3 + 50)]
    for n, lo in cases:
        p = find_prime(n, lo)
        mu, etas = subgroup_and_etas(p, n)
        m = (p - 1) // n
        absA = np.abs(etas[1:])          # |eta_b| for b=1..p-1 (M ranges over b!=0)
        M = absA.max()
        sqn = np.sqrt(n)
        beta = np.log(p) / np.log(n)
        floor_target = np.sqrt(n * np.log(p / n))
        print(f"n={n} p={p} m={m} beta={beta:.2f}  M={M:.3f}  sqrt(n)={sqn:.3f}  "
              f"M/sqrt(n)={M/sqn:.3f}  M/sqrt(n ln(p/n))={M/floor_target:.3f}")

        # ---- Q1: DIRECTION test. Welch/Levenshtein are LOWER bounds. -----------------
        # The unweighted 2k-moment over b!=0:  S_k = sum_{b!=0} |eta_b|^{2k}.
        # Parseval (k=1): sum_{b in F_p} |eta_b|^2 = p*n (exact). With b=0 term n^2:
        S1_all = np.abs(etas)**2
        parseval = S1_all.sum()
        print(f"   [Parseval] sum_b|eta_b|^2 = {parseval:.1f}   p*n = {p*n}   "
              f"(b=0 term n^2={n*n}) -> off-principal sum = {parseval - n*n:.1f}  p*n-n^2={p*n - n*n}")
        # Welch lower bound on MAX over the FAMILY {eta_b/sqrt(n)} (m-1 nonzero distinct cosets):
        # max coherence >= sqrt((Nfam - L)/(L(Nfam-1))) with L=n length, Nfam = #distinct nonzero cosets = m
        # This is a LOWER bound; it tells you the family CAN'T be flatter than this. NOT an upper bound.
        Nfam = m  # eta is constant on cosets b*mu_n -> m distinct nonzero values
        welch_lower_coh = np.sqrt(max(0.0,(Nfam - n)/(n*(Nfam - 1)))) if Nfam > 1 else 0.0
        # translate coherence to |eta|: |eta_b| = n * coherence (since seqs have norm sqrt(n), <S_b,S_b'>=eta, /n)
        welch_lower_M = n * welch_lower_coh
        print(f"   [Q1 direction] Welch LOWER bound on family max |eta| = {welch_lower_M:.3f}  "
              f"(true M={M:.3f}).  Welch is a >= bound; we NEED <=.  "
              f"{'LOWER<=true OK as lower bd' if welch_lower_M <= M+1e-6 else 'VIOLATION'}")

        # ---- Q2: best UPPER bound from any NONNEG weight on the moment ----------------
        # The honest weighted-moment UPPER bound that IS valid:  for any nonneg weight w_b>=0,
        #    w_{b*} * M^{2k} <= sum_b w_b |eta_b|^{2k}  =: WM_k(w),
        # where b* is the argmax. So  M^{2k} <= WM_k(w)/w_{b*} for ANY w.
        # The BEST such bound is achieved by w concentrated on b*  -> recovers M trivially (needs knowing b*).
        # The lemma instead restricts w to "positive combos of additive chars OFF mu_n" and uses w_min.
        # Test the *intended* version: w = a fixed analyzable weight; bound = (WM_k/w_min)^{1/(2k)}.
        # Natural Levenshtein-flavoured weights to test (all WITHOUT knowing b*):
        #   (a) uniform w=1 (recovers unweighted power-mean = the trap)
        #   (b) w_b = |eta_b|^{2}/floor  (self-weighting; NOT allowed by lemma but is the *optimal* over-weight)
        #   (c) w_b from a positive additive-char combo off mu_n: w_b = |sum_{x in mu_n} e_p(b x)|^2-shaped? that IS eta.
        for k in [1, 2, 3, 4]:
            A2k = absA**(2*k)
            # (a) uniform: power-mean
            unif = (A2k.mean())**(1.0/(2*k))
            # (b) self-optimal over-weight w_b = |eta_b|^{2}  (the dream weight)
            wt = absA**2
            WM = (wt * A2k).sum()
            wmin_b = wt.min()
            # bound = (WM / wmin)^{1/(2k)} ; but wmin~0 (most cosets near 0) -> blows up. Use w on SUPPORT.
            # Instead: the only meaningful bound is WM / w_{b*}. self-weight gives w_{b*}=M^2:
            bound_selfopt = (WM / (M**2))**(1.0/(2*k))
            print(f"   k={k}: unweighted power-mean (E|eta|^2k)^(1/2k) = {unif:.3f}  "
                  f"[ratio to M {unif/M:.3f}]   |   self-optimal-weight bound = {bound_selfopt:.3f}  "
                  f"[ratio to M {bound_selfopt/M:.3f}]")
        print()

if __name__ == "__main__":
    main()
