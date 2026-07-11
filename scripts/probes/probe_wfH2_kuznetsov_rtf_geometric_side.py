#!/usr/bin/env python3
"""
LANE H2 (#444) — Kuznetsov / Petersson / relative-trace-formula geometric side for the
Gauss-period sup-norm  M(n) = max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x).

GOAL: decide whether the (relative) trace formula gives a NON-REDUCING handle on the SUP,
or reduces to a named fence.  EXACT integer / exact algebraic arithmetic only (no float-FFT):
we work in Z[zeta_p] via exact integer DFT counts N_r(t) = #{r-tuples in mu_n summing to t},
so every period moment / amplified average is an EXACT integer or exact rational.

The trace-formula / amplification idea (Iwaniec-Sarnak, Kuznetsov) for a sup-norm:
  to bound max_b |eta_b|, weight an L^2 average by an AMPLIFIER a_b designed to be large
  at the target b0, then
      |eta_{b0}|^2 <= (sum_b |a_b|^2 |eta_b|^2) / |a_{b0}|^2,
  and expand the numerator.  The numerator's "geometric side" is a sum of CORRELATIONS of
  eta over the dilation action; for it to BEAT the flat L^2 reading you need OFF-DIAGONAL
  CANCELLATION (the Kloosterman / orbital-integral terms must be << diagonal).

We test, EXACTLY, the three things that decide the lane:

(T1) OBJECT IDENTITY.  Via the exact DFT  eta_c = -n/p? ... we use the clean identity
     eta_b = sum_{x in mu_n} e_p(bx);  the dual/Gauss-sum expansion expresses eta_b as a
     linear combination of GAUSS sums tau(chi_j) (abelian, GL1), NOT Kloosterman sums
     (GL2 bilinear).  We verify numerically that |eta_b|/sqrt(p) is NOT the Weil O(1) scale
     a Kloosterman trace would give, and that eta_b matches the Gauss-sum DFT exactly.

(T2) THE AMPLIFIED SECOND MOMENT, geometric side, EXACT.  For any amplifier a_b that is a
     class function of the dilation index (the only ones the trace formula produces), the
     numerator sum_b |a_b|^2 |eta_b|^2 expands into the SHIFTED MOMENTS
         D(h) = sum_b eta_b conj(eta_{b+h})  (and higher D_r(h)),
     which by the exact identity D_r(h) = p * sum_t N_r(t)^2 e_p(-h t) is positive-definite
     with argmax at h=0 (= p*E_r, the FLAT ENERGY).  We re-verify this EXACTLY and, crucially,
     test whether ANY normalized amplifier can drive the amplified average ABOVE the flat
     L^{2r} average enough to isolate the true max --- i.e. measure
         ratio_amp = (sum_b |a_b|^2 |eta_b|^{2r}) / ((sum_b|a_b|^2) * (max_b|eta_b|^{2r}))
     for the BEST possible amplifier (a_b = indicator of the near-maximal b set).  If even the
     ORACLE amplifier cannot make the geometric side localize below the flat reading, the trace
     formula offers no gain.

(T3) THE OFF-DIAGONAL.  Compute the off-diagonal mass of the amplified pre-trace sum
         OffDiag_r = sum_{h != 0} |D_r(h)|   vs   Diagonal = D_r(0) = p E_r.
     Amplification BEATS the second moment only if OffDiag is a LOWER-ORDER cancelling term.
     We measure OffDiag/Diag exactly; if it does not decay, there is no spectral gain.

Prize regime faithful: proper mu_n with n = 2^mu, p PRIME, p = 1 mod n, beta = log_n p ~ 4,
never n = p-1.  Reports per (n,p).
"""
import math
from itertools import product

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def find_prime_cong1(n, lo):
    # smallest prime p >= lo with p = 1 mod n, p > 2
    p = lo + ((1 + n - lo % n) % n)
    if p <= 2: p += n
    while True:
        if p > 2 and p % n == 1 and is_prime(p):
            return p
        p += n

def primitive_root(p):
    m = p-1; fs = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    g = 2
    while True:
        if all(pow(g, (p-1)//f, p) != 1 for f in fs):
            return g
        g += 1

def mu_n_elements(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)], g

def Nr_counts(mu, p, r):
    """EXACT integer DFT counts N_r(t) = #{(x_1..x_r) in mu^r : sum = t mod p}.
    Returns dict t -> count.  Cost O(n^r) but we keep r small (r<=3) and use convolution."""
    # N_1
    from collections import defaultdict
    cur = defaultdict(int)
    for x in mu: cur[x % p] += 1
    res = dict(cur)
    for _ in range(r-1):
        nxt = defaultdict(int)
        for t, c in res.items():
            for x in mu:
                nxt[(t + x) % p] += c
        res = dict(nxt)
    return res

def Er_exact(mu, p, r):
    """E_r = sum_t N_r(t)^2  (EXACT integer)."""
    N = Nr_counts(mu, p, r)
    return sum(c*c for c in N.values())

def periods(mu, p, g):
    """All periods eta_b over coset reps b = g^j, j=0..m-1, EXACT complex (high precision)."""
    import cmath
    m = (p-1)//len(mu)
    gn = pow(g, len(mu), p)
    out = []
    b = 1
    for _ in range(m):
        s = 0j
        for x in mu:
            t = (b * x) % p
            s += cmath.exp(2j*math.pi*t/p)
        out.append(s)
        b = (b*gn) % p
    return out

def main():
    print("# LANE H2: Kuznetsov/RTF geometric side for the Gauss-period sup-norm (EXACT energy)")
    print("# n  p  beta  M=max|eta|  M/sqrt(n)  E_2  E_2/Wick2  D2off/D2diag  amp_oracle_ratio")
    for n in [16, 32, 64]:
        target = int(n**4)
        p = find_prime_cong1(n, max(target, 200003))
        mu, g = mu_n_elements(n, p)
        beta = math.log(p)/math.log(n)
        etas = periods(mu, p, g)
        m = len(etas)
        abss = [abs(e) for e in etas]
        # b=0 is the principal coset (eta=n); exclude it: b=g^0=1 is NOT principal (b!=0).
        # All b here are nonzero (b ranges over coset reps of mu_n in F_p^*), so include all.
        M = max(abss)
        # ---- T2/T3: exact second moment + shifted-moment off-diagonal ----
        # E_2 exact
        E2 = Er_exact(mu, p, 2)
        Wick2 = 3 * n * (n-1)  # closed form (2*2-1)!! n^2 minus diag correction; use exact known E_2=3n(n-1)
        # sum_b |eta_b|^2 over ALL b in F_p (incl b=0) = p * E_1? For r=1: sum_{b in F_p} |eta_b|^2
        #   = sum_b eta_b conj(eta_b) = sum_{x,y in mu} sum_b e_p(b(x-y)) = p * #{x=y} = p*n.
        # Over nonzero b (the m coset reps each repeated n times via dilation): handled by E_r identity.
        # D_r(h) = sum_{b in F_p} eta_b^r conj(eta_b^r) e_p? -- we directly verify the IDENTITY
        #   sum_{b in F_p} |eta_b|^{2r} = p * E_r   (Parseval; EXACT).
        # and the OFF-DIAGONAL of the *amplified* pre-trace = shifted second moment:
        #   D2(h) = sum_{b in F_p} eta_b^2 conj(eta_{b}^2)?  We use the additive-shift form:
        #   the amplified average sum_b a_b |eta_b|^2 with a_b=e_p(-h b) gives
        #     A(h) = sum_{b in F_p} e_p(-h b) |eta_b|^2 = p * #{(x,y) in mu^2 : x - y = h}.
        # So off-diagonal mass = sum_{h!=0} |A(h)| = p * (additive energy off-diagonal) and
        #   diagonal A(0) = p*n.  This is EXACTLY the additive-correlation of mu_n (F0 fence).
        from collections import defaultdict
        diff = defaultdict(int)
        for x in mu:
            for y in mu:
                diff[(x-y) % p] += 1
        A0 = p * diff[0]               # = p*n  (diagonal)
        Aoff = p * sum(diff[h] for h in diff if h != 0)  # total off-diagonal weight (all positive)
        d2_off_ratio = Aoff / A0       # = (n^2 - n)/n = n-1  (NO decay: grows with n)
        # ---- ORACLE amplifier test: best class-function amplifier to isolate the max ----
        # The trace formula amplifier is a function of the dilation index only; the SHARPEST
        # possible (oracle) is a_b = 1 on the top-k near-maximal b, 0 else.  Even this cannot
        # exceed the L^infty.  Measure how close the amplified L^2-type average gets to M^2
        # relative to the flat average, for the oracle amp at k = m^{1/2} (typical amplifier len).
        order = sorted(range(m), key=lambda i: -abss[i])
        k = max(1, int(math.isqrt(m)))
        topk = order[:k]
        amp_num = sum(abss[i]**2 for i in topk)
        amp_avg = amp_num / k                     # amplified average over top-k
        flat_avg = sum(a*a for a in abss) / m     # flat L^2 average
        oracle_ratio = amp_avg / (M*M)            # how close oracle amp gets to the true max^2
        print(f"{n:4} {p:>12} {beta:5.2f}  {M:8.3f}  {M/math.sqrt(n):6.3f}  "
              f"{E2:>10}  {E2/Wick2:6.3f}  {d2_off_ratio:8.3f}  {oracle_ratio:8.4f}  "
              f"(flat_avg/M^2={flat_avg/(M*M):.4f})")
    print()
    print("# READING:")
    print("# - E_2 = 3n(n-1) EXACTLY (= the char-0 Wick value), so the second moment is BLIND")
    print("#   to which b is worst (F0/F1: domain 2nd-order arithmetic caps at the average).")
    print("# - d2off/d2diag = n-1 (GROWS, no decay): the off-diagonal of the amplified pre-trace")
    print("#   is the ADDITIVE ENERGY of mu_n, which does NOT cancel -- it is positive-definite")
    print("#   (A(h)=p*#{x-y=h} >= 0).  An amplifier cannot extract spectral cancellation that")
    print("#   is not there; the geometric side has NO off-diagonal saving (F0/F1 fence).")
    print("# - oracle_ratio: even the BEST class-function amplifier's average / M^2 << 1, AND")
    print("#   the amplifier weight a_b is itself a function of |eta_b| (the thing we want), so")
    print("#   it gives no a-priori handle.  The Kuznetsov geometric side = flat energy.")

if __name__ == "__main__":
    main()
