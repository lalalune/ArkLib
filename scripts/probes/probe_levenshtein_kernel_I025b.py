#!/usr/bin/env python3
"""
I025b — the ACTUAL Levenshtein mechanism (orthogonal-polynomial weighted kernel), tested for
whether it can be turned into an UPPER bound on M(mu_n).

Background (faithful to Levenshtein 1999 / Boztas):
  For a code/sequence-family viewed as points u_b on the sphere (here unit vectors v_b = S_b/||S_b||
  in C^n, S_b(t)=e_p(b zeta^t)), define the moment of the (signed) Gram measure against a
  weight polynomial f(t)=sum_l f_l Q_l(t) (Q_l = Gegenbauer/Krawtchouk, t = <v_i,v_j> = inner product).
  Levenshtein's bound: if f(t)<=0 for all t in [-1, s] (s = max off-diag inner product = coherence)
  and f_l>=0 (positive Gegenbauer coeffs) and f_0>0, then
        Nfam <= f(1) / f_0.
  This is a LOWER bound on coherence s (upper bound on family size), via LP duality (Delsarte).
  The "weighted higher moment" = choosing f as a positive Gegenbauer combination of DEGREE up to k.
  It beats Welch (degree-1 f) by a moment-DEPTH factor.

THE DECISIVE QUESTION for the prize: Levenshtein/Delsarte LP bounds the COHERENCE s of a family
GIVEN its size Nfam (a LOWER bound on s, equivalently an upper bound on packing). The prize needs
an UPPER bound on s = M/n for the FIXED family mu_n. LP-duality bounds go the packing direction.

This probe makes the duality concrete and checks the two things that could rescue I025:
  (R1) Does the Levenshtein LP bound, with f a degree-k positive Gegenbauer combo, EVER yield an
       UPPER bound on the coherence of OUR specific family (not just a generic packing lower bound)?
  (R2) The over-weight dream: among all probability weights nu on the off-principal frequencies b
       (weights we are allowed to write down without knowing argmax), is there one for which the
       weighted 2k-th moment / weight-of-worst-freq beats the exponent 1-o(1) i.e. gives M <= poly?
       We test the *upper* envelope sup_nu  [ (sum_b nu_b |eta_b|^{2k})^{1/2k} ] vs M and vs sqrt(n),
       restricting nu to be a positive additive-character combination (the lemma's allowed class).

HONESTY: proper subgroup mu_n=2^mu, n|p-1, p PRIME, p>>n^3, never n=p-1.
"""
import numpy as np
import sympy

def find_prime(n, lo):
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and sympy.isprime(p):
            return p
        p += 1

def setup(p, n):
    g0 = sympy.primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    mu = np.array([pow(g, i, p) for i in range(n)])
    w = np.exp(2j * np.pi * np.arange(p) / p)
    etas = np.array([w[(b * mu) % p].sum() for b in range(p)], dtype=complex)
    return mu, etas

def main():
    print("=== I025b: Levenshtein orthogonal-poly kernel as UPPER bound? ===\n")
    for n, lo in [(8, 8**3+50), (16, 16**3+50), (32, 32**3+50)]:
        p = find_prime(n, lo)
        mu, etas = setup(p, n)
        m = (p - 1)//n
        absA = np.abs(etas[1:])
        M = absA.max()
        sqn = np.sqrt(n)
        print(f"n={n} p={p} m={m}  M={M:.3f}  M/sqrt(n)={M/sqn:.3f}")

        # ---- R2: the allowed-weight envelope. ------------------------------------------
        # The lemma permits nu_b = a positive additive-character combination supported OFF mu_n:
        #   nu_b = | sum_{a in A} c_a e_p(a b) |^2  with A a fixed set, c_a complex (this is >=0).
        # Equivalently nu_b = (a positive-definite function of b). The KEY constraint: a weight you
        # can WRITE DOWN cannot already encode argmax_b|eta_b| (that's the whole open problem).
        # Test the most aggressive *legitimate* over-weight: nu = a positive-definite kernel that
        # concentrates on a coset structure (Gauss/Fejer kernel). Compare best achievable bound.
        #
        # Build candidate weights nu (all valid: nonneg, computable, off-principal):
        cand = {}
        cand["uniform"] = np.ones(p-1)
        # Fejer-type kernel centered at every freq is uniform; a kernel concentrated near a TARGET
        # coset requires knowing the target. The honest "best legitimate" weight is the one matched
        # to the |eta| profile WITHOUT pointwise access: nu_b = (mean of |eta| over the dilation
        # orbit of b)^2  -- but |eta| is constant on cosets b*mu_n already, so orbit-averaging is identity.
        # So the only freedom is a positive function of the COSET index c in Z/m. Test nu = best
        # positive-definite function on Z/m maximizing the resulting bound's TIGHTNESS to M, i.e. the
        # Levenshtein-optimal Gegenbauer weight on the coset-correlation values.
        # Coset values: |eta| takes one value per coset c=0..m-1.
        g0 = sympy.primitive_root(p); gg = pow(g0, 1, p)
        # coset rep b = g0^c ; |eta_{g0^c}|
        coset_abs = np.array([np.abs(etas[pow(g0, c*m, p)]) for c in range(n)])  # n cosets? no:
        # b ranges over F_p*, eta_b depends only on b mod mu_n i.e. on coset b*mu_n in F_p*/mu_n (m cosets).
        # representative b_c = g0^c, c=0..m-1
        coset_abs = np.array([np.abs(etas[pow(g0, c, p)]) for c in range(m)])
        Mc = coset_abs.max()
        # weighted 2k-moment over the m cosets with weight nu_c>=0 (each coset has n elements -> factor n cancels)
        for k in [1, 2, 4, 8]:
            v2k = coset_abs**(2*k)
            # uniform power mean
            unif = (v2k.mean())**(1.0/(2*k))
            # BEST legitimate over-weight that does NOT peek at argmax: we are allowed any nu that is a
            # positive-definite function of the coset index. The extreme legitimate choice concentrates as
            # much as positive-definiteness allows. Positive-definite on Z/m with nu>=0 in BOTH domains is
            # very restrictive (Bochner): the tightest is nu_c proportional to a SQUARED character sum.
            # Test nu_c = |eta_{coset c}|^2-derived is ILLEGAL (peeks). Legitimate proxy: nu = Fejer^j on Z/m.
            # Fejer kernel of order j: nu_c = (sum_{|l|<j} (1-|l|/j) omega^{c l})  >=0, concentrates near c=0.
            # But "near c=0" is an arbitrary target; the worst freq is not at c=0. So Fejer gives NO gain
            # unless re-centered on argmax (illegal). Demonstrate: best over ALL shifts of Fejer = peeking.
            j = max(2, m // 4)
            l = np.arange(-(j-1), j)
            tri = 1 - np.abs(l)/j
            # Fejer centered at shift s0:  nu_c = sum_l tri[l] cos(2 pi (c - s0) l / m)
            best_bound = np.inf
            for s0 in range(0, m, max(1, m//16)):  # sample shifts (peeking would scan all -> argmax)
                cc = np.arange(m)
                nu = np.array([np.sum(tri * np.cos(2*np.pi*((c - s0) * l)/m)) for c in cc])
                nu = np.maximum(nu, 0)  # clip to nonneg (still a valid weight after clipping? approx)
                if nu.sum() == 0: continue
                nu = nu / nu.sum()
                WM = (nu * v2k).sum()
                # valid upper bound only against the weight at the SUPPORTED worst coset:
                # M^{2k} <= WM / nu_{argmax};  but if nu_{argmax}=0 the bound is vacuous.
                amax = int(np.argmax(coset_abs))
                if nu[amax] <= 1e-12: continue
                b = (WM / nu[amax])**(1.0/(2*k))
                best_bound = min(best_bound, b)
            print(f"   k={k}: unweighted (mean|eta_c|^2k)^(1/2k)={unif:.3f} [/M {unif/M:.3f}] | "
                  f"best legit-Fejer-weight upper bound={best_bound:.3f} [/M {best_bound/M:.3f}] "
                  f"(<M means GAIN; >=M means no gain)")
        print()

if __name__ == "__main__":
    main()
