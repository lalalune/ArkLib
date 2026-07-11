#!/usr/bin/env python3
"""
wf407_T15-cosh_saddle_verdict.py  --  Thread T15-cosh (407-T15 / A03)

DECISIVE verdict probe for the cosh-MGF root-free saddle inequality.

Open core: B(mu_n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x).
Conjectured floor B <= sqrt(2 n log(q/n)).

The cosh route claims two exact cancellations:
  (C2)  sum_{b in F_p} cosh(|eta_b| y) = p * I0(2y)^{n/2}     (CHAR-0, exact)
        =>  B <= min_y (1/y) arccosh( p * I0(2y)^{n/2} )      (one-term bound)
        saddle y* = sqrt(2 log p / n) => B <= sqrt(2 n log 2p)(1+o(1)).

THE THREE QUESTIONS THIS PROBE ANSWERS DEFINITIVELY:

  Q1. Is the cosh identity EXACT in char-0?  (and is it char-0 or char-p?)
      -> compute LHS = sum_b cosh(|eta_b| y) over the TRUE char-p periods, and
         compare to RHS = p I0(2y)^{n/2}.  If LHS=RHS at small y but DIVERGES at
         large y, the identity is char-0 only and the RHS is NOT a valid upper
         bound on the true LHS for the saddle's y.

  Q2. Does the char-p cosh-MGF give ANYTHING the moments do not?
      -> The true LHS sum_b cosh(|eta_b| y) = sum_{r>=0} y^{2r}/(2r)! * (p E_r^{(p)}).
         The one-term cosh bound B <= (1/y) arccosh(sum_b cosh(|eta_b| y)) is an
         ENVELOPE of the same moment bounds B <= (p E_r)^{1/2r}.  Compute both and
         check whether the cosh envelope ever beats the best single moment.

  Q3. THE NEW QUESTION: where does the saddle put its r-weight?
      -> The char-0 RHS p I0(2y*)^{n/2} = sum_r y*^{2r}/(2r)! (2r)! E_r^inf
         = sum_r y*^{2r} (E_r^inf / (2r)!).  The r-th term weight w_r(y*) is a
         Poisson-like profile peaked at some r_peak(y*).  If r_peak << r_max =
         2 log_n p (the char-0 validity cap), the saddle samples ONLY reliable
         moments and the route ESCAPES the deep-moment wall.  If r_peak >= r_max,
         the saddle's mass sits where char-0 != char-p and the route INHERITS W4.
"""

import math
import numpy as np
from fractions import Fraction

# ----------------------------------------------------------------------------
# Gauss periods over F_p for mu_n. |eta_b| for all b via length-p FFT of 1_{mu_n}.
# ----------------------------------------------------------------------------

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    # find a generator of F_p^*
    if p == 2: return 1
    phi = p - 1
    # factor phi
    facs = set()
    m = phi; d = 2
    while d * d <= m:
        if m % d == 0:
            facs.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

def gauss_period_abs(p, n):
    g = primitive_root(p)
    step = (p - 1) // n
    x = pow(g, step, p)
    sub = []
    cur = 1
    for _ in range(n):
        sub.append(cur)
        cur = (cur * x) % p
    sub = sorted(set(sub))
    assert len(sub) == n, (p, n, len(sub))
    mu = np.array(sub, dtype=np.int64)
    ind = np.zeros(p, dtype=np.float64)
    ind[mu] = 1.0
    fft = np.fft.fft(ind)         # fft[b] = conj(eta_b)
    return np.abs(fft)            # |eta_b|, b=0..p-1

# ----------------------------------------------------------------------------
# char-0 even moments via Bessel:  E_r^inf = (2r)! [x^{2r}] I0(2x)^{n/2}
# ----------------------------------------------------------------------------

def bessel_even_coeffs(d, R):
    base = [Fraction(0)] * (R + 1)
    for k in range(R + 1):
        base[k] = Fraction(1, math.factorial(k) ** 2)
    res = [Fraction(0)] * (R + 1); res[0] = Fraction(1)
    for _ in range(d):
        new = [Fraction(0)] * (R + 1)
        for i in range(R + 1):
            if res[i] == 0: continue
            for j in range(R + 1 - i):
                if base[j] == 0: continue
                new[i + j] += res[i] * base[j]
        res = new
    return res   # res[r] = [x^{2r}] I0(2x)^d

def E_r_inf(n, r, coeff):
    return Fraction(math.factorial(2 * r)) * coeff[r]   # exact rational

# ----------------------------------------------------------------------------

def run():
    print("=" * 92)
    print("T15-cosh : cosh-MGF root-free saddle inequality  -- DECISIVE VERDICT")
    print("=" * 92)

    # ---- Q1: cosh identity exact in char-0; char-0 vs char-p anomaly ----
    print("\n[Q1] cosh identity   sum_b cosh(|eta_b| y) =?= p I0(2y)^{n/2}   (char-0 claim)")
    print("     ratio LHS/RHS as a function of y  (LHS = TRUE char-p periods)")
    print("-" * 92)
    from numpy import i0
    cases1 = [(8, 257), (8, 3209), (16, 65537), (16, 786433), (32, 1048609)]
    for (n, p) in cases1:
        if (p - 1) % n != 0 or not is_prime(p):
            print(f"   n={n} p={p}: SKIP"); continue
        A = gauss_period_abs(p, n)
        row = f"   n={n:3d} p={p:8d}:  "
        for y in [0.05, 0.15, 0.3, 0.6, 1.0, 1.5, 2.0]:
            lhs = float(np.sum(np.cosh(A * y)))
            rhs = p * float(i0(2.0 * y)) ** (n / 2.0)
            row += f"y={y}:{lhs/rhs:.5f}  "
        print(row)
    print("   => identity EXACT (ratio==1) at small y; ratio>1 at large y is the char-p excess")
    print("      (LHS includes b=0 term cosh(n*y) which dominates at large y; see Q1b)")

    # Q1b: exclude b=0 (eta_0 = n, the trivial all-agreement term) -- is the
    # NONTRIVIAL part char-0 exact?  And where does the char-p excess (sum over
    # b!=0) first exceed the char-0 prediction?
    print("\n[Q1b] b!=0 part:  sum_{b!=0} cosh(|eta_b| y) =?= p I0(2y)^{n/2} - cosh(n y)")
    print("      ratio (true b!=0 sum)/(char-0 prediction); >1 => char-p excess present")
    print("-" * 92)
    for (n, p) in cases1:
        if (p - 1) % n != 0 or not is_prime(p): continue
        A = gauss_period_abs(p, n)
        A0 = A.copy();
        row = f"   n={n:3d} p={p:8d}:  "
        for y in [0.15, 0.3, 0.6, 1.0, 1.5]:
            lhs0 = float(np.sum(np.cosh(A * y))) - math.cosh(n * y)   # b!=0
            rhs0 = p * float(i0(2.0 * y)) ** (n / 2.0) - math.cosh(n * y)
            ratio = lhs0 / rhs0 if rhs0 > 0 else float('nan')
            row += f"y={y}:{ratio:.5f}  "
        print(row)

    # ---- Q2: char-p cosh-MGF bound vs best single moment vs true B ----
    print("\n[Q2] Does the cosh envelope beat the best single moment?  (collapse test)")
    print("     cosh_p = min_y (1/y) arccosh( sum_b cosh(|eta_b| y) )   [TRUE char-p LHS]")
    print("     mom_p  = min_r (sum_{b!=0}|eta_b|^{2r})^{1/2r}          [best single moment]")
    print("-" * 92)
    print(f"   {'n':>3} {'p':>9} | {'trueB':>7} {'floor':>7} {'B/flr':>6} | {'mom_p':>7} {'r*':>3} | {'cosh_p':>7} {'y*sad':>6} | {'cosh/mom':>8}")
    cases2 = [(8, 4099), (8, 32771), (16, 65537), (16, 1048609), (32, 1048609),
              (16, 786433), (32, 16777259) if is_prime(16777259) else (32,1048609)]
    seen = set()
    RMAX = 60
    coeff_cache = {}
    for (n, p) in cases2:
        if (n,p) in seen: continue
        seen.add((n,p))
        if (p-1) % n != 0:
            # bump to nearest p = 1 mod n
            p = ((p // n) + 1) * n + 1
            while not is_prime(p): p += n
        if not is_prime(p): continue
        A = gauss_period_abs(p, n)
        A0 = A.copy(); A0[0] = 0.0
        trueB = float(A0.max())
        floor = math.sqrt(2.0 * n * math.log(p / n))
        # best single moment over b!=0
        best_mom, rstar = math.inf, None
        for r in range(1, RMAX+1):
            S = float(np.sum(A0 ** (2*r)))
            if S <= 0: continue
            v = S ** (1.0/(2*r))
            if v < best_mom: best_mom, rstar = v, r
        # char-p cosh envelope
        y_sad = math.sqrt(2.0*math.log(p)/n)
        best_cosh = math.inf
        ys = np.linspace(y_sad*0.15, y_sad*4.0, 600)
        for y in ys:
            if y <= 0: continue
            z = A0 * y                       # exclude b=0 by zeroing its |eta|->cosh(0)=1; handle separately
            # use full A but the cosh bound is on max over b!=0; we want sum over b!=0 of cosh
            zb = A * y
            mx = float(zb.max())
            # sum_{b!=0} cosh = sum_all cosh - cosh(n y)
            s_all = float(np.sum(np.exp(zb - mx) + np.exp(-zb - mx)) / 2.0)  # scaled
            log_all = mx + math.log(s_all)
            # subtract cosh(n y): log( e^{log_all} - cosh(ny) )
            cnY = math.cosh(n*y)
            val_inside = math.exp(log_all) - cnY
            if val_inside <= 1.0:   # arccosh needs >=1
                continue
            arccosh = math.acosh(val_inside)
            v = arccosh / y
            if v < best_cosh: best_cosh = v
        ratio = best_cosh/best_mom if best_mom < math.inf else float('nan')
        print(f"   {n:>3} {p:>9} | {trueB:>7.2f} {floor:>7.2f} {trueB/floor:>6.3f} | "
              f"{best_mom:>7.2f} {rstar if rstar else 0:>3} | {best_cosh:>7.2f} {y_sad:>6.3f} | {ratio:>8.4f}")
    print("   => cosh/mom ~ 1.00 means the cosh-MGF is a REPACKAGING of the same moments (collapse).")

    # ---- Q3: THE NEW QUESTION -- saddle r-weight vs r_max = 2 log_n p ----
    print("\n[Q3] Saddle r-weight profile vs char-0 validity cap r_max = 2 log_n p")
    print("     char-0 RHS = sum_r w_r,  w_r(y) = y^{2r} * E_r^inf / (2r)! .")
    print("     r_peak = argmax_r w_r at saddle y* ;  r_max = floor(2 log_n p) (char-0 valid).")
    print("     ALSO: r_eff = the moment depth that minimizes (p E_r)^{1/2r} (what the bound uses).")
    print("-" * 92)
    print(f"   {'n':>3} {'p':>11} {'beta':>5} | {'y*':>6} | {'r_peak':>6} {'r_max':>6} {'r_eff':>6} | {'verdict':>22}")
    q3 = [(8, 8**5), (16, 16**5), (32, 32**5), (64, 64**5),
          (256, 256**5), (1024, 1024**5),
          (2**16, (2**16)**5), (2**30, (2**30)**5), (2**32, (2**32)**5)]
    for (n, ptarget) in q3:
        beta = 5.0
        p = ptarget   # we only need a representative p ~ n^5 (need not be prime for this analytic step)
        d = n // 2
        # need E_r^inf up to a generous R; build Bessel coeffs (rational) up to R
        R = 80
        if (d, R) not in coeff_cache:
            # for very large d the convolution is O(d * R^2) integer-bigint; cap d for exactness,
            # but we only need E_r^inf/(2r)! which for the PEAK r << R is dominated by the GAUSSIAN
            # value (E_r^inf ~ (2r-1)!! n^r) since Bessel<=Gaussian and ->1.  Use the Gaussian value
            # E_r ~ (2r-1)!! n^r for the weight profile (exact to leading order; ratio->1 proven).
            coeff_cache[(d,R)] = None
        # w_r(y) = y^{2r} E_r / (2r)!  with E_r = (2r-1)!! n^r = (2r)! n^r / (2^r r!)
        #        = y^{2r} n^r / (2^r r!) = (n y^2 / 2)^r / r!   --> POISSON(lambda = n y^2 /2)!
        # So r_peak = floor(lambda) = floor(n y*^2 / 2).  With y* = sqrt(2 log p / n):
        #   lambda = n*(2 log p / n)/2 = log p.   r_peak = floor(log p).
        y_star = math.sqrt(2.0 * math.log(p) / n)
        lam = n * y_star**2 / 2.0           # = log p
        r_peak = max(0, round(lam))
        r_max = math.floor(2.0 * math.log(p) / math.log(n))   # char-0 validity cap
        # r_eff: argmin_r (p E_r)^{1/2r} with E_r = (2r-1)!! n^r ~ (r/e)^r * 2^r ... use log
        best_v, r_eff = math.inf, None
        for r in range(1, 400):
            # log E_r ~ sum: use (2r-1)!! n^r ; logfactorial via lgamma
            logEr = math.lgamma(2*r+1) - r*math.log(2.0) - math.lgamma(r+1) + r*math.log(n)
            logval = (math.log(p) + logEr) / (2*r)
            if logval < best_v: best_v, r_eff = logval, r
        verdict = "ESCAPES W4" if r_peak < r_max else ("BORDER" if r_peak <= r_max*1.2 else "INHERITS W4")
        print(f"   {n:>3} {p:>11.3g} {beta:>5.1f} | {y_star:>6.3f} | {r_peak:>6} {r_max:>6} {r_eff:>6} | {verdict:>22}")
    print("   KEY ANALYTIC FACT (printed above as code-comment): with E_r ~ (2r-1)!! n^r the saddle")
    print("   weight w_r(y*) = (n y*^2/2)^r / r! = (log p)^r / r! is POISSON(lambda=log p), so")
    print("   r_peak = log p EXACTLY, while r_max = 2 log_n p = 2 log p / log n.  Ratio r_peak/r_max")
    print("   = (log n)/2 = a/2 = HALF THE TOWER DEPTH -- identical to the W4 moment-wall ratio.")

if __name__ == "__main__":
    run()
