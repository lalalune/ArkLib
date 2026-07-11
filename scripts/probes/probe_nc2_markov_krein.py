#!/usr/bin/env python3
"""
probe_nc2_markov_krein.py  (DO NOT COMMIT)

CENTRAL TEST of the Markov-Krein / moment-problem extremal family for #444.

WALL: M(n) = max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x),  mu_n = 2-power
subgroup of F_p, |mu_n| = n = 2^mu ~ p^{1/4}. Want M(n) <= C sqrt(n log p).

The FAMILY's claim (to be tested ruthlessly):
  The empirical measure nu = (1/(q-1)) sum_{b != 0} delta_{eta_b^2}  on [0, B^2] has
  raw moments  m_r = (1/(q-1)) sum_{b!=0} eta_b^{2r}  =  (q E_r - n^{2r})/(q-1)
  where E_r = E_r(mu_n) is the char-0 Wick energy (PROVEN <= (2r-1)!! n^r).
  Markov-Krein bounds the SUPPORT MAX of a measure given its first R moments.

The obstruction: a per-conjugate bound gives (2r)^{n/2}; only inter-conjugate
cancellation (= sqrt cancellation) wins. The question: does the Markov-Krein bound
from AGGREGATE (b-averaged) moments give sqrt -- AND is that legitimate, or does it
secretly require the char-p moments to match char-0 (= the open transfer)?

This probe does the EXACT computation over real finite fields:
  1. Build eta_b for all b, compute the TRUE max M(n).
  2. Compute the aggregate moments m_r (these are q-DEPENDENT, the real ones).
  3. Compute the CHAR-0 moments m_r^{char0} = E_r (the PROVEN ones the family wants
     to use, divided appropriately).
  4. Apply the principal-representation / Markov-Krein upper bound on max-support
     from the first R moments, using (a) the true moments, (b) the char-0 moments.
  5. KEY DIAGNOSTIC: does the Markov-Krein max-support bound from char-0 moments
     equal/exceed/undershoot the true M(n)? If it UNDERSHOOTS the true M(n) using
     char-0 moments, the family is REFUTED (char-0 moments do NOT bound the true max
     -- the char-p excess is load-bearing). If it gives sqrt only when char-p
     moments are fed, it = the open transfer.
"""
import numpy as np
from math import gcd, log, sqrt

def factor_2power(q):
    # multiplicative order structure: largest 2-power dividing q-1
    m = q - 1
    e = 0
    while m % 2 == 0:
        m //= 2
        e += 1
    return e  # 2^e | q-1

def find_prime_with_2power(target_n, beta):
    """Find prime q ~ target_n^beta with 2^mu | q-1, n = 2^mu close to target_n."""
    import sympy
    mu = int(round(log(target_n, 2)))
    n = 2**mu
    # want q = k*n + 1 prime, q ~ target_n^beta
    qtarget = int(target_n**beta)
    k = max(2, qtarget // n)
    for _ in range(200000):
        q = k*n + 1
        if sympy.isprime(q):
            return q, n, mu
        k += 1
    return None, n, mu

def subgroup(q, n):
    """Return the n-element 2-power subgroup of F_q^* as a list of residues."""
    import sympy
    g = sympy.primitive_root(q)
    order = q - 1
    h = pow(g, order // n, q)  # element of order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % q
    return S

def gauss_periods(q, S):
    """eta_b = sum_{x in S} exp(2 pi i b x / q) for b = 0..q-1. Return |eta_b| real array."""
    S = np.array(S, dtype=np.int64)
    bs = np.arange(q)
    # eta_b = sum_x e(b x / q); compute via outer product mod q
    # (q up to ~1e6, |S| small) -> matrix (q, n)
    ang = 2*np.pi/q * (np.outer(bs, S) % q)
    eta = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
    return np.abs(eta)

def char0_energy(n, r):
    """E_r(mu_n) char-0 = #{(x1..x_2r) in mu_n^{2r} : sum eps... } the additive energy
    of order r. For r=1: E_1 = n (count of x=y). For general r the PROVEN Wick bound is
    (2r-1)!! n^r. We compute the EXACT char-0 E_r combinatorially for small n via the
    vanishing-sum count over the cyclotomic integers (here we just use the proven Wick
    UPPER bound (2r-1)!! n^r as the 'best char-0 moment' the family is allowed)."""
    from math import prod
    dfact = 1
    for k in range(1, 2*r, 2):
        dfact *= k
    return dfact * n**r   # (2r-1)!! n^r  -- the PROVEN char-0 ceiling

def markov_krein_max_from_moments(moments):
    """Given raw moments m_0=1, m_1, ..., m_{2R} (m_0 normalized to 1) of a probability
    measure on [0, infinity), the principal representation / classical moment bound on
    the maximal support point. We use the 'upper principal representation' tail bound:
    the largest atom L of the upper principal representation satisfies the Hankel
    determinant condition. A SIMPLE, RIGOROUS upper certificate on the support max:
       For ANY measure with these moments, max-support >= m_{r+1}/m_r for all r
       (ratio lower bound), and the smallest UPPER bound consistent with moments via
       the (2x2) Cauchy-Schwarz on the tail. The clean Markov-Krein extremal value for
       max support given moments m_1..m_{2R} is the LARGEST root of the orthogonal
       polynomial wrt the moment sequence (Gauss quadrature node). We compute that."""
    # Build Hankel matrix and get the largest Gauss-quadrature node (= largest root of
    # the degree-R orthogonal polynomial). This is the Markov-Krein principal-rep MAX
    # atom -- the canonical 'extreme value given moments' answer.
    R = (len(moments)-1)//2
    H = np.empty((R+1, R+1))
    for i in range(R+1):
        for j in range(R+1):
            H[i, j] = moments[i+j]
    # Golub-Welsch: build Jacobi matrix from moments via Cholesky of Hankel
    try:
        Lc = np.linalg.cholesky(H)
    except np.linalg.LinAlgError:
        return None  # moments not PSD (numerical)
    # nodes = eigenvalues of the Jacobi matrix; largest = max support of the
    # canonical representation. Construct Jacobi via orthonormal polynomials.
    # Use the recurrence from Cholesky factor (standard).
    # Simpler robust route: nodes are generalized eigenvalues of (H1, H0) shifted Hankels.
    H0 = np.empty((R, R)); H1 = np.empty((R, R))
    for i in range(R):
        for j in range(R):
            H0[i, j] = moments[i+j]
            H1[i, j] = moments[i+j+1]
    try:
        ev = np.linalg.eigvals(np.linalg.solve(H0, H1))
        ev = ev[np.isfinite(ev)].real
        return ev.max() if len(ev) else None
    except np.linalg.LinAlgError:
        return None

def run(target_n, beta, R):
    q, n, mu = find_prime_with_2power(target_n, beta)
    if q is None:
        print(f"  no prime for n~{target_n} beta={beta}")
        return
    S = subgroup(q, n)
    assert len(set(S)) == n, "subgroup wrong size"
    abseta = gauss_periods(q, S)
    abseta_nz = abseta[1:]  # b != 0
    Mtrue = abseta_nz.max()
    sqrtbound = sqrt(n * log(q))
    print(f"\nn={n} (2^{mu})  q={q}  beta=logq/logn={log(q)/log(n):.2f}")
    print(f"  TRUE M(n) = max_b!=0 |eta_b| = {Mtrue:.3f}")
    print(f"  sqrt(n log q) = {sqrtbound:.3f}   ratio M/sqrt = {Mtrue/sqrtbound:.3f}")
    print(f"  2 sqrt(n) = {2*sqrt(n):.3f}   ratio M/2sqrtn = {Mtrue/(2*sqrt(n)):.3f}")

    # TRUE aggregate moments of eta_b^2 over b!=0  (q-dependent, the real ones)
    e2 = abseta_nz**2
    m_true = [1.0] + [np.mean(e2**r) for r in range(1, 2*R+1)]
    # CHAR-0 moments the family WANTS to use: m_r = E_r (proven Wick ceiling)
    # The b-averaged moment is (1/(q-1)) sum_{b!=0} eta_b^{2r} = (q E_r - n^{2r})/(q-1).
    # Family's claim: use char-0 E_r. Build the char-0-derived aggregate moment.
    m_char0 = [1.0]
    for r in range(1, 2*R+1):
        Er = char0_energy(n, r)            # proven ceiling (2r-1)!! n^r
        magg = (q*Er - n**(2*r))/(q-1)     # the b-averaged 2r-th moment from char-0 E_r
        m_char0.append(magg)

    mk_true = markov_krein_max_from_moments(m_true)
    mk_char0 = markov_krein_max_from_moments(m_char0)
    print(f"  Markov-Krein max-atom (TRUE moments, R={R}):   {mk_true}")
    if mk_true: print(f"      sqrt of that = {sqrt(max(mk_true,0)):.3f}  (compare M(n)={Mtrue:.3f})")
    print(f"  Markov-Krein max-atom (CHAR-0 moments, R={R}): {mk_char0}")
    if mk_char0: print(f"      sqrt of that = {sqrt(max(mk_char0,0)):.3f}  (compare M(n)={Mtrue:.3f})")

    # DECISIVE DIAGNOSTIC
    if mk_char0 is not None:
        bound_from_char0 = sqrt(max(mk_char0, 0))
        if bound_from_char0 < Mtrue - 1e-6:
            print(f"  >>> CHAR-0 moment bound {bound_from_char0:.3f} UNDERSHOOTS true M(n)={Mtrue:.3f}")
            print(f"  >>> => char-0 moments do NOT bound the true max. char-p excess load-bearing. FAMILY DODGE FAILS.")
        else:
            print(f"  >>> char-0 bound {bound_from_char0:.3f} >= M(n). (consistent but is it sqrt? ratio to sqrt(n log q) = {bound_from_char0/sqrtbound:.3f})")

    # Also: how far is TRUE moment seq from char-0? (the char-p excess at each r)
    print(f"  excess ratio m_true/m_char0 by r:", end=" ")
    for r in range(1, R+1):
        print(f"r{r}:{m_true[r]/m_char0[r]:.3f}", end=" ")
    print()

if __name__ == "__main__":
    print("="*70)
    print("MARKOV-KREIN MOMENT-PROBLEM FAMILY TEST (#444)")
    print("="*70)
    for tn, beta in [(8, 3.0), (16, 2.5), (16, 4.0), (32, 2.0), (32, 3.0), (64, 2.0)]:
        for R in [2, 3, 4]:
            run(tn, beta, R)
