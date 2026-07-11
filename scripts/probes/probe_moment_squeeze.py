#!/usr/bin/env python3
r"""Probe (#407 ISOLATE-A-QUANTITY) — moment SQUEEZE on the period spectrum.

OBJECT.  n = 2^mu, p prime with n | p-1, m = (p-1)/n.  The m REAL Gaussian
periods  eta_i = sum_{x in mu_n} e_p(g^i x)  (i = 0..m-1, one per nonzero coset
of mu_n in F_p^*) form a single Galois orbit of real algebraic integers; they
are the roots of an integer polynomial P(x) = prod_i (x - eta_i) of degree m.

EXACT POWER SUMS of the m periods (these are the KNOWN data):
  M_1            = sum_i eta_i             = -1                       (trace)
  M_{2k+1}       = sum_i eta_i^{2k+1}      = -n^{2k}   (k>=1)         (odd, EXACT)
  M_{2r}         = sum_i eta_i^{2r}        = p*E_r - n^{2r}           (even)
       where E_r = #{(a_1..a_2r) in mu_n^{2r} : a_1+..+a_r = a_{r+1}+..+a_{2r}}.
  E_1 = n,  E_2 = 3n^2-3n,  E_3 = 15n^3-45n^2+40n  (char-0, prize regime).

  [Derivation: sum_{b in F_p} S_b^j = p * T_j with T_j = #{j-tuples of mu_n
   summing to 0 mod p}; S_0 = n; the m periods are S_b for b ranging over coset
   reps, so M_j = (p*T_j - n^j)/n * ... -- but periods are SUMMED over coset, so
   sum over the m periods of eta_i^j = sum_{b!=0} S_b^j / (multiplicity)... we
   compute M_j DIRECTLY and exactly from the actual eta_i via integer arithmetic
   below, and CROSS-CHECK against the closed forms.]

THE UNKNOWN.  M := max_i |eta_i|.  Johnson per-word = sqrt(n).  Floor = sqrt(2 n log m).
The meta-theorem says M is NOT determined by finitely many moments (needs r ~ log m).

THE SQUEEZE TRICK (this probe).  The EVEN moments M_{2r} = sum eta_i^{2r} are the
absolute even moments of the empirical measure nu = (1/m) sum delta_{eta_i}.
Define mu_{2r} = M_{2r}/m (= integral of |eta|^{2r} dnu).  Two classical facts:

  (LC)  log-convexity / Lyapunov:  the sequence  r |-> log mu_{2r}  is CONVEX in
        the index, equivalently  mu_{2r}^2 <= mu_{2r-2} * mu_{2r+2}, AND
        mu_{2r}^{1/(2r)} is NON-DECREASING with limit M = max|eta_i|.
  (CS)  Cauchy-Schwarz on ODD interpolation:  mu_{2r-1}^2 <= mu_{2r-2} mu_{2r},
        where mu_{2r-1} = integral |eta|^{2r-1} dnu is the ABSOLUTE odd moment.

  *** CRUX of the trick ***  Our odd power sums M_{2k+1} = -n^{2k} are SIGNED, not
  absolute.  |M_{2k+1}| = n^{2k} is a LOWER bound for the absolute odd moment
  sum  A_{2k+1} := sum_i |eta_i|^{2k+1}  (triangle ineq: |sum| <= sum|.|).  So the
  EXACT odd data gives  A_{2k+1} >= n^{2k}, i.e.  mu^{abs}_{2k+1} >= n^{2k}/m.

  Chain:   even moments give an UPPER scaffold via (LC); the signed-odd lower
  bound A_{2k+1} >= n^{2k} feeds (CS) as a LOWER constraint on the even moments
  it brackets:  mu_{2r} >= (mu^{abs}_{2r-1})^2 / mu_{2r-2} >= (n^{2r-2}/m)^2/mu_{2r-2}.
  Iterate.  Q: does [lower(2r), upper(2r)] CLOSE (ratio -> 1) so that
  M = lim mu_{2r}^{1/(2r)} is PINNED, beating sqrt(n)?  Or does it BLOW UP?

OUTPUT (exact integer arithmetic for all M_j and E_r):
  - exact M_j cross-checked against closed forms (odd = -n^{2k}, even = pE_r-n^{2r})
  - the squeeze interval [L_{2r}, U_{2r}] for the even moment M_{2r} obtained from
    log-convexity (upper, Hankel-PSD) and signed-odd-CS (lower)
  - the implied bracket on M = max|eta| at the largest reliable r
  - verdict: does the exact-odd squeeze DETERMINE the even moments / bound M ?
"""
import math
from fractions import Fraction
import sys
import numpy as np

# ----------------------------------------------------------------------------
# exact number theory helpers (no sympy)
# ----------------------------------------------------------------------------
def isprime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d, r = n-1, 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def primeat(n, beta):
    """smallest prime p >= n^beta with n | p-1."""
    target = int(n**beta)
    p = target - (target % n) + 1
    if p <= target: p += n
    while not isprime(p):
        p += n
    return p

def factor(m):
    f = []; d = 2
    while d*d <= m:
        while m % d == 0:
            f.append(d); m//=d
        d += 1
    if m > 1: f.append(m)
    return set(f)

def primitive_root(p):
    fs = factor(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")

def subgroup_mu(p, n):
    """mu_n = the 2^mu-th roots of unity in F_p (the multiplicative subgroup of order n)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S = []; x = 1
    for _ in range(n):
        S.append(x); x = (x*h) % p
    assert len(set(S)) == n
    return S, g

# ----------------------------------------------------------------------------
# EXACT periods as real algebraic numbers via high-precision, and EXACT power
# sums M_j via integer convolution (the closed forms).
# ----------------------------------------------------------------------------
def _convolve_j(p, n, S, j):
    """j-fold subset-sum count distribution over F_p, as a numpy int64 vector.
       cnt[c] = #{(a_1..a_j) in mu_n^j : sum a_i = c mod p}.  Max cell value n^j;
       for our ranges (n<=32, j<=13) n^j can exceed int64 only at the extreme; we
       use object dtype when n^j > 2^62 to stay EXACT."""
    use_obj = (n**j) > (1 << 61)
    dt = object if use_obj else np.int64
    cnt = np.zeros(p, dtype=dt); cnt[0] = 1
    Sarr = list(S)
    for _ in range(j):
        new = np.zeros(p, dtype=dt)
        for s in Sarr:
            new += np.roll(cnt, s)
        cnt = new
    return cnt

def E_r_exact(p, n, S, r):
    """E_r = sum_c (#{r-subset-sum of mu_n equal to c})^2  (exact integer)."""
    cnt = _convolve_j(p, n, S, r)
    # exact sum of squares via python ints
    return int(sum(int(c)*int(c) for c in cnt.tolist()))

def T_j_exact(p, n, S, j):
    """T_j = #{j-tuples of mu_n summing to 0 mod p} (exact integer)."""
    cnt = _convolve_j(p, n, S, j)
    return int(cnt[0])

def power_sums_exact(p, n, S, jmax):
    """M_j = sum over the m periods of eta_i^j, EXACT integers.
       Identity: sum_{b in F_p} S_b^j = p * T_j, where S_b = sum_{x in mu_n} e_p(bx).
       S_0 = n.  The m periods are exactly {S_b : b in (one rep per coset of mu_n)};
       each nonzero coset value of b gives the SAME S_b for all n members? NO --
       S_b depends on b only through the coset b*mu_n, and there are m=(p-1)/n cosets,
       each represented n times among b!=0.  So sum_{b!=0} S_b^j = n * M_j.
       Hence  n*M_j + n^j = p*T_j  =>  M_j = (p*T_j - n^j)/n. """
    M = {}
    for j in range(1, jmax+1):
        Tj = T_j_exact(p, n, S, j)
        num = p*Tj - n**j
        assert num % n == 0, (j, num, n)
        M[j] = num // n
    return M

# ----------------------------------------------------------------------------
# direct numeric periods (for cross-check of max|eta| = M)
# ----------------------------------------------------------------------------
def periods_numeric(p, n, S, g):
    import cmath
    m = (p-1)//n
    w = 2*math.pi/p
    eta = []
    b = 1
    seen = set()
    # iterate b over coset reps: b = g^i for i=0..m-1 gives distinct cosets
    gm = pow(g, m, p)  # not needed; just step b by g, dedup cosets
    reps = []
    used = [False]*p
    bb = 1
    for i in range(p-1):
        if not used[bb]:
            reps.append(bb)
            for x in S:
                used[(bb*x) % p] = True
        bb = (bb*g) % p
    assert len(reps) == m, (len(reps), m)
    for r in reps:
        s = sum(cmath.exp(1j*w*((r*x) % p)) for x in S)
        eta.append(s.real)
    return eta

# ----------------------------------------------------------------------------
# THE SQUEEZE.
# Given exact even moments M2[r] = sum eta_i^{2r} (r=1..R) and exact odd lower
# bounds A_odd[k] = |M_{2k+1}| = n^{2k}  (<= true absolute odd moment sum),
# build two-sided brackets on the even moments and on M = max|eta|.
# ----------------------------------------------------------------------------
def _is_psd(Mmat, tol=-1e-7):
    """numpy PSD test on a symmetric float matrix (smallest eigenvalue >= tol)."""
    w = np.linalg.eigvalsh(np.array(Mmat, dtype=float))
    return float(w.min()), float(w.max())

def squeeze(p, n, m, Mall, Reven):
    r"""HONEST two-sided squeeze.

    Mall: dict j -> M_j = sum over the m periods of eta_i^j, EXACT, j=1..2*Reven+1.
          Odd ones are the EXACT prize data (-1, -n^{2k}); even ones are derived
          from E_r.  In the "isolate" game we ask whether the ODD data + LOW even
          data PIN the HIGHER even data / M.  We therefore report, for each r,
          what the lower-order constraints FORCE, and compare to the true value.

    The legitimate one-sided bounds (let a_j = (abs) moment sum = sum|eta|^j; for
    even j a_j = M_j; |M_{2k+1}| = n^{2k} <= a_{2k+1}):

      (CS, valid lower bound on the NEXT even moment, needs an UPPER bound U_{2k}
       on the current even moment as denominator):
          a_{2k+2} >= a_{2k+1}^2 / a_{2k} >= (n^{2k})^2 / U_{2k}.
       The only a-priori upper bound on a_{2k} not using higher data is the
       MAX cap a_{2k} <= m * M^{2k}; circular.  Using the EXACT a_{2k}=M_{2k} as
       denominator gives the SHARP CS lower bound on M_{2k+2} from the odd datum
       a_{2k+1} -- we report THAT (it isolates the *gap* the odd datum leaves).

      (max vs average):  M = max|eta| satisfies
          (M_{2r}/m)^{1/2r}  <=  M  <=  (M_{2r})^{1/2r}.
       lower uses average, upper uses the trivial sum>=max^{2r}.  Both need M_{2r}.

      (Hamburger determinacy):  the FULL set of measures with moments
       m_0..m_{2R} (m_0=1, m_j=M_j/m) consistent with support in [-B,B] is the
       Chebyshev-Markov band; the SUPPORT extremes are pinned by the moment
       matrices.  We compute, for the EXACT normalized moments, the largest
       atom location forced/allowed: max support point xmax of any rep measure.
       The Hankel matrix  H = [m_{i+j}]_{0<=i,j<=R}  must be PSD (it is, exact
       data).  The UPPER edge of support of the *minimal* representing measure is
       the largest root of the orthogonal polynomial p_{R+1}; the principal
       representation gives the tightest band [x_-, x_+] containing ALL atoms of
       SOME representing measure -- i.e. the moment data ALONE cannot force M
       below x_+ (the Markov upper extreme) nor above it.  We compute x_+ from the
       Jacobi/Hankel data and compare to the true M.  If x_+ >> sqrt(n) the moment
       data is UNDERDETERMINED (M free up to x_+); if x_+ ~ true M, pinned.
    """
    res = {}
    # ---- normalized moments m_j = M_j / m (m_0 = 1) ----
    mom = {0: Fraction(1)}
    for j in sorted(Mall):
        mom[j] = Fraction(Mall[j], m)

    # ---- (A) sharp CS lower bound on each even moment from the odd datum below ----
    # a_{2k+2} >= (n^{2k})^2 / M_{2k}  (uses EXACT M_{2k}; lower bound on M_{2k+2}).
    csL = {}
    for k in range(1, Reven):
        if 2*k in Mall and 2*k+2 in Mall:
            denom = Fraction(Mall[2*k])
            if denom > 0:
                csL[k+1] = Fraction(n**(2*k))**2 / denom   # lower bound on M_{2k+2}
    res['csL'] = csL

    # ---- (B) Hamburger / Chebyshev-Markov upper support extreme from Hankel data ----
    # Build Hankel matrix H0 = [m_{i+j}]_{i,j=0..R} and H1 = [m_{i+j+1}] (need odd
    # moments too -> use the signed normalized odd moments, EXACT).
    R = Reven
    have = all((i in mom) for i in range(0, 2*R+1))
    markov_xplus = None
    hankel_min_eig = None
    if have:
        H0 = [[float(mom[i+j]) for j in range(R+1)] for i in range(R+1)]
        emin, emax = _is_psd(H0)
        hankel_min_eig = emin
        # The largest support point of any [B]-bounded representing measure: the
        # Chebyshev-Markov upper principal representation places an atom at the
        # largest generalized eigenvalue of (H1, H0)-type pencils.  Simplest sharp
        # proxy: x_+ = largest root of the degree-(R+1) monic orthogonal polynomial
        # for the moment functional, = largest eigenvalue of the Jacobi matrix J_R
        # built from m_0..m_{2R}.  Compute J via Cholesky of H0 (Gram) -> recurrence.
        try:
            # orthonormal polynomial recurrence (Stieltjes via Cholesky of Hankel)
            import numpy.linalg as la
            H0n = np.array(H0)
            # eigenvalues of the (R)x(R) Hankel give the support of the discrete
            # measure with R atoms matching m_0..m_{2R-1}; its MAX eigen-ratio is the
            # Gauss-quadrature top node = sharpest moment-forced upper support point.
            # Build truncated Jacobi from modified Chebyshev / Stieltjes:
            beta_j = []; alpha_j = []
            # use the three-term recurrence via inner products with the EXACT moments
            # (monomials).  P_{-1}=0, P_0=1.  We track coefficient vectors.
            polys = [np.array([1.0])]  # P_0 = 1
            def ip(a, b):
                # <a,b> = sum_k m_{deg} ... compute via moment of product
                prod = np.polynomial.polynomial.polymul(a, b)
                return sum(float(mom.get(d, 0))*c for d, c in enumerate(prod))
            P0 = polys[0]; norm2_prev = ip(P0, P0)
            xP = np.array([0.0, 1.0])  # x
            a0 = ip(np.polynomial.polynomial.polymul(P0, xP), P0)/norm2_prev
            alpha_j.append(a0)
            # P_1 = (x - a0) P_0
            P1 = np.polynomial.polynomial.polysub(np.polynomial.polynomial.polymul(P0, xP), a0*P0)
            polys.append(P1)
            Pprev, Pcur = P0, P1
            norm2_cur = ip(P1, P1)
            for k in range(1, R):
                bk = norm2_cur/norm2_prev
                beta_j.append(bk)
                ak = ip(np.polynomial.polynomial.polymul(Pcur, xP), Pcur)/norm2_cur
                alpha_j.append(ak)
                Pnext = np.polynomial.polynomial.polysub(
                    np.polynomial.polynomial.polysub(
                        np.polynomial.polynomial.polymul(Pcur, xP), ak*Pcur),
                    bk*np.polynomial.polynomial.polyval if False else bk*np.concatenate([Pprev, [0,0]])[:max(len(Pcur)+1,len(Pprev))]
                )
                # simpler: Pnext = (x-ak)Pcur - bk Pprev
                Pnext = np.polynomial.polynomial.polysub(
                    np.polynomial.polynomial.polymul(Pcur, np.array([-ak,1.0])), bk*Pprev)
                Pprev, Pcur = Pcur, Pnext
                norm2_prev = norm2_cur; norm2_cur = ip(Pcur, Pcur)
            # Jacobi matrix (R x R)
            Jm = np.diag(alpha_j[:R])
            for i in range(len(beta_j[:R-1])):
                b = math.sqrt(abs(beta_j[i]))
                Jm[i, i+1] = b; Jm[i+1, i] = b
            nodes = np.linalg.eigvalsh(Jm)
            markov_xplus = float(nodes.max())
        except Exception as e:
            markov_xplus = ('err', str(e))
    res['hankel_min_eig'] = hankel_min_eig
    res['markov_xplus'] = markov_xplus
    return res

def fmt(x):
    if isinstance(x, Fraction):
        return f"{float(x):.6g}"
    return f"{x:.6g}"

def run(n, beta, max_even_r=6):
    p = primeat(n, beta)
    S, g = subgroup_mu(p, n)
    m = (p-1)//n
    beta_eff = math.log(p)/math.log(n)
    print(f"\n=== n={n}  p={p}  m=(p-1)/n={m}  beta={beta_eff:.3f}  log2(m)={math.log2(m):.2f} ===")

    # exact power sums up to a moderate order
    jmax = 2*max_even_r + 1
    M = power_sums_exact(p, n, S, jmax)

    # verify odd closed forms and even closed forms
    print(" exact power sums M_j = sum_i eta_i^j  (i over the m periods):")
    print(f"   M_1 = {M[1]}   (closed form -1: {'OK' if M[1]==-1 else 'FAIL'})")
    for k in range(1, max_even_r):
        j = 2*k+1
        cf = -(n**(2*k))
        print(f"   M_{j} = {M[j]:>22}   -n^{2*k}={cf:>22}   {'OK' if M[j]==cf else 'MISMATCH'}")
    # even closed form: M_{2r} = sum over m periods of eta^{2r} = (p*E_r - n^{2r})/n
    #   (E_r counts over mu_n^{2r}; sum_{b!=0} eta_b^{2r} = p E_r - n^{2r} = n * M_{2r})
    Eclosed = {1: n, 2: 3*n*n-3*n, 3: 15*n**3-45*n*n+40*n}
    for r in range(1, max_even_r+1):
        j = 2*r
        Er = E_r_exact(p, n, S, r)
        cf_even = (p*Er - n**(2*r)) // n
        ok = (M[j] == cf_even) and ((p*Er - n**(2*r)) % n == 0)
        extra = ""
        if r in Eclosed:
            extra = f"  E_{r}={Er} (closed {Eclosed[r]}: {'OK' if Er==Eclosed[r] else 'DIFF'})"
        print(f"   M_{j} = {M[j]:>20}   (pE_{r}-n^{2*r})/n={cf_even:>20}   {'OK' if ok else 'MISMATCH'}{extra}")

    # ground-truth M = max|eta|
    eta = periods_numeric(p, n, S, g)
    Mmax = max(abs(e) for e in eta)
    print(f" GROUND TRUTH  M = max_i|eta_i| = {Mmax:.6f}   sqrt(n)={math.sqrt(n):.4f}  "
          f"ratio M/sqrt(n)={Mmax/math.sqrt(n):.4f}  floor sqrt(2n ln m)={math.sqrt(2*n*math.log(m)):.4f}")

    # ----- the squeeze -----
    Meven = {r: M[2*r] for r in range(1, max_even_r+1)}
    sq = squeeze(p, n, m, M, max_even_r)
    csL = sq['csL']

    # (A) sharp CS lower bound on each even moment from the ODD datum just below it
    print(" SQUEEZE (A): CS lower bound on M_{2r} from EXACT odd M_{2r-1}=-n^{2r-2}"
          "  (a_{2r} >= (n^{2r-2})^2 / M_{2r-2}):")
    print(f"   {'2r':>4} {'CS_lower(M_2r)':>18} {'M_2r TRUE':>20} {'CS/TRUE':>9}"
          f" {'CS->M=(L/m)^1/2r':>18} {'TRUE->(M/m)^1/2r':>18}")
    for r in range(2, max_even_r+1):
        L = csL.get(r)
        if L is None: continue
        true = Meven[r]
        ratio = float(L)/true if true != 0 else float('nan')
        implM = (float(L)/m)**(1.0/(2*r)) if L > 0 else float('nan')
        trueM = (true/m)**(1.0/(2*r))
        print(f"   {2*r:>4} {fmt(L):>18} {true:>20} {ratio:>9.4f} {implM:>18.4f} {trueM:>18.4f}")

    # (B) max-vs-average bracket on M from EACH exact even moment
    print(" SQUEEZE (B): rigorous bracket on M=max|eta| from EXACT even moment M_{2r}:")
    print(f"   {'2r':>4} {'lower=(M_2r/m)^1/2r':>20} {'upper=(M_2r)^1/2r':>18} "
          f"{'gap=up/lo':>10} {'true M':>9}")
    best_lo, best_up = 0.0, float('inf')
    for r in range(1, max_even_r+1):
        true = Meven[r]
        lo = (true/m)**(1.0/(2*r))
        up = true**(1.0/(2*r))
        best_lo = max(best_lo, lo); best_up = min(best_up, up)
        print(f"   {2*r:>4} {lo:>20.4f} {up:>18.4f} {up/lo:>10.2f} {Mmax:>9.4f}")
    print(f"   tightest bracket over r: [{best_lo:.4f}, {best_up:.4f}]  (true M={Mmax:.4f}); "
          f"gap factor up/lo = {best_up/best_lo:.3f}")

    # (C) Chebyshev-Markov / Hankel upper support extreme: what M the FULL moment
    #     sequence (up to 2R, incl. the exact odd) ALLOWS as the largest atom.
    xplus = sq['markov_xplus']
    print(" SQUEEZE (C): Chebyshev-Markov upper support extreme x_+ from moments m_0..m_{2R}"
          f" (R={max_even_r}, Hankel min-eig={sq['hankel_min_eig']}):")
    if isinstance(xplus, float):
        print(f"   x_+ (largest atom any rep. measure can place) = {xplus:.4f}; "
              f"true M={Mmax:.4f}; sqrt(n)={math.sqrt(n):.4f}; x_+/sqrt(n)={xplus/math.sqrt(n):.4f}")
    else:
        print(f"   x_+ = {xplus}")

    # ----- verdict numbers -----
    print(" >>> ISOLATE SUMMARY:")
    print(f"     Johnson per-word = sqrt(n) = {math.sqrt(n):.4f}")
    print(f"     true M = {Mmax:.4f}  (M/sqrt(n) = {Mmax/math.sqrt(n):.4f})")
    print(f"     moment LOWER bound on M (best, EXACT even data) = {best_lo:.4f}  "
          f"=> {'>= sqrt(n)' if best_lo>=math.sqrt(n) else '< sqrt(n)'} "
          f"({best_lo/math.sqrt(n):.3f}x)")
    print(f"     moment UPPER bound on M (best, EXACT even data) = {best_up:.4f}")
    print(f"     CS-from-odd alone gives a lower bound on M_2 of "
          f"{(float(csL.get(2,0))/m)**(1.0/4) if csL.get(2) else 0:.4f} at 2r=4")
    return dict(p=p, n=n, m=m, Mmax=Mmax,
                M_low_best=best_lo, M_up_best=best_up,
                markov_xplus=xplus if isinstance(xplus, float) else None,
                sqrtn=math.sqrt(n))

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    if args.quick:
        cases = [(8, 4.0, 6)]
    else:
        cases = [
            (8,  4.0, 6),
            (8,  4.5, 6),
            (16, 4.0, 6),
            (16, 4.5, 5),
            (32, 4.0, 5),
        ]
    results = []
    for n, beta, R in cases:
        try:
            results.append(run(n, beta, R))
        except Exception as e:
            print(f"  [n={n} beta={beta} FAILED: {e}]")
    print("\n================ SUMMARY ================")
    print(f"{'n':>4}{'p':>9}{'m':>7}{'M_true':>9}{'sqrt(n)':>9}{'M/sqn':>7}"
          f"{'mom_lo':>9}{'lo/sqn':>8}{'mom_up':>9}{'markov_x+':>11}{'x+/sqn':>8}")
    for r in results:
        mx = r['markov_xplus']
        print(f"{r['n']:>4}{r['p']:>9}{r['m']:>7}{r['Mmax']:>9.3f}{r['sqrtn']:>9.3f}"
              f"{r['Mmax']/r['sqrtn']:>7.3f}{r['M_low_best']:>9.3f}"
              f"{r['M_low_best']/r['sqrtn']:>8.3f}{r['M_up_best']:>9.3f}"
              f"{(mx if mx else float('nan')):>11.3f}{(mx/r['sqrtn'] if mx else float('nan')):>8.3f}")
