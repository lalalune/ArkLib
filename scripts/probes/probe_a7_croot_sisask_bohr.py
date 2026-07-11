"""
A7 [croot-sisask] — Almost-periodicity / Bohr-set forcing of the worst-case far-line incidence.

THE NEW LEMMA (invented here, to be tested):
  The far-line incidence  N(u0) = |Ball| + S(u0),  S(u0) = sum_{xi in D} K_w(wt xi) e_p(xi.u0)
  is (Croot-Sisask) almost-periodic in u0: there is a Bohr set B = B(Gamma, rho) of bounded
  rank |Gamma| = O(eps^{-2} log(1/alpha)) such that  |S(u0 + t) - S(u0)| <= eps * ||...||  for all
  t in B.  HOPE ("Bohr-set forcing"): B is large enough that translating the worst u0* by a suitable
  t in B lands inside the bulk where N ~ avg, hence  N(u0*) <= 2 * avg = the floor (past Johnson).

  We reduce to the EXACT prize core (the manifesto's reduction): the worst-case far-line incidence
  is governed by  M(mu_n) = max_{b != 0} |f(b)|,  f(b) = sum_{x in mu_n} e_p(b x).   This f(b) is
  the simplest faithful realization of S (it IS the autocorrelation Fourier transform of 1_{mu_n}),
  so we test the Croot-Sisask program ON THE PERIOD f, which is exactly  1_{mu_n}-hat.

  Concretely f = FT(1_{mu_n}).  Define g(b) = |f(b)|^2 = FT of the AUTOCORRELATION (= n * 1_{mu_n}
  convolved with its reflection) = the convolution 1_C * 1_{-C} -hat.  The "worst u0" <-> the
  worst b = argmax |f(b)|.  The Bohr-set forcing claim becomes:

     (Q1) Is there a large Bohr set B (built from the large Fourier spectrum of 1_{mu_n}, i.e. the
          large values of f) such that f is almost-constant under translation by t in B?
     (Q2) Does the worst-case b* admit an almost-period t in B carrying it into the bulk
          (|f| ~ avg ~ sqrt(n))?  I.e. does the worst case ESCAPE the Bohr set (no gain) or get
          DOMINATED by it (the floor)?

  HORN PREDICTION: almost-periodicity makes the PEAK ROBUST (many near-equal peaks at b* + B),
  which is the OPPOSITE of forcing it down. We test which actually happens, prize-faithfully.

Prize-faithful: p PRIME, p = 1 mod n, mu_n PROPER (n | p-1, (p-1)/n > 1), p >> n^3 (beta>=4),
NEVER n = p-1.
"""
import math
import numpy as np

def isprime(x):
    if x < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
        if x % q == 0: return x == q
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def fac(x):
    f = set(); d = 2
    while d*d <= x:
        while x % d == 0: f.add(d); x //= d
        d += 1
    if x > 1: f.add(x)
    return f

def proot(p):
    fs = fac(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g

def find_prime(n, beta):
    p = (n**beta) | 1
    while True:
        if isprime(p) and (p-1) % n == 0 and (p-1)//n > 1:
            return p
        p += 2

def build(n, beta):
    p = find_prime(n, beta)
    g = proot(p); h = pow(g, (p-1)//n, p)
    mu = [pow(h, i, p) for i in range(n)]
    ind = np.zeros(p)
    for x in mu: ind[x] = 1.0
    F = np.fft.fft(ind)          # F[b] = sum_x e^{-2pi i b x / p}  ; |F[b]| = |f(b)| = period magnitude
    a = np.abs(F)
    return p, mu, h, F, a

print("="*108)
print("A7 Croot-Sisask Bohr-set forcing of the worst far-line incidence (= worst period |f(b)|).")
print("="*108)

# ---------------------------------------------------------------------------
# PART 1.  The Bohr set of almost-periods of the period f, and the worst-case b*.
#   An almost-period of order eps for f (in sup-norm relative to the floor sqrt(n)) is a t such that
#       max_b | f(b+t) - f(b) |  <=  eps * sqrt(n).
#   We ask: how large is the set of eps-almost-periods T_eps?  And is the worst b* "movable" by a
#   t in T_eps toward the bulk?  Croot-Sisask asserts |T_eps| >= p/2 for eps ~ O(1) and that T_eps
#   contains a Bohr set of the large-spectrum frequencies of 1_{mu_n}.  We MEASURE both, exactly.
# ---------------------------------------------------------------------------
print("\nPART 1 — almost-period set size (eps=1.0 in sqrt(n) units), floor M, worst-case dilation orbit")
print(" n     p          M=maxb|f|  floor=sqrt(2 n ln(p/n))  M/floor  |T_{1.0}|/p  bstar  dilate-peak?")
for a_exp in range(3, 6):
    n = 2**a_exp
    beta = 4
    p, mu, h, F, a = build(n, beta)
    a0 = a.copy(); a0[0] = 0.0
    M = a0.max()
    bstar = int(np.argmax(a0))
    floor = math.sqrt(2.0 * n * math.log(p / n))
    # almost-period set for eps=1.0 (in units of sqrt(n)): t such that max_b|f(b+t)-f(b)| <= eps*sqrt(n).
    # Instead of a full O(p) roll per t (too slow for large p), measure ||tau_t f - f||_2^2 EXACTLY by
    # Parseval: ||tau_t F - F||_2^2 = sum_b |F[b]|^2 |e(b t/p)-1|^2 = 2 sum_b |F[b]|^2 (1 - cos(2pi b t/p)).
    # The sup-norm almost-period is harder; the L2 almost-period set is what Croot-Sisask actually controls,
    # so we measure the L2 version (favorable to the claim). t is an L2-eps-almost-period iff
    #   ||tau_t f - f||_2 <= eps * sqrt(n) * sqrt(p)   (RHS = eps * ||f||_2 since ||f||_2^2 = n*p).
    eps = 1.0
    pw = np.abs(F)**2                      # |F[b]|^2 ; sum = n*p
    bb = np.arange(p)
    rs = np.random.RandomState(0)
    ts = rs.randint(1, p, size=min(p-1, 1000))
    cnt = 0; tot = 0
    for t in ts:
        tot += 1
        # ||tau_t f - f||_2^2 = 2 sum_b |F[b]|^2 (1 - cos(2 pi b t / p))
        d2 = 2.0 * np.sum(pw * (1.0 - np.cos(2*math.pi * ((bb * int(t)) % p) / p)))
        if d2 <= (eps**2) * (n * p): cnt += 1
    Tfrac = cnt / max(tot, 1)
    # dilation: |f| is invariant under b -> c*b for c in the multiplier subgroup mu_{(p-1)/n}? Check |f(h*b*)|.
    same = abs(a0[(h*bstar) % p] - M) < 1e-6
    print(" %-4d  %-10d %-9.3f  %-22.3f  %-7.3f  %-11.4f  %-6d %s"
          % (n, p, M, floor, M/floor, Tfrac, bstar, "dilation-fixed-peak" if same else "moves"))

# ---------------------------------------------------------------------------
# PART 2.  THE DECISIVE TEST: does the worst-case b* ESCAPE the Bohr set, or is it DOMINATED?
#   Croot-Sisask forcing would need: every u0 (every b) is reachable from the bulk by an almost-period,
#   so that worst <= 2*avg.  We test the contrapositive directly.
#   For the WORST b*, look at the value of |f| on the Bohr-set translates b* + B.  If almost-periodicity
#   holds AT b*, then |f| stays ~ M on the whole coset b*+B  => the peak is a ROBUST PLATEAU, the OPPOSITE
#   of being forced to the average.  If instead b* is ISOLATED (|f| collapses to avg immediately off b*),
#   then b* is NOT an almost-period center and the Bohr set never reaches it.  Either way: NO forcing.
# ---------------------------------------------------------------------------
print("\nPART 2 — the worst-case peak vs the Bohr set: plateau (robust) or isolated (escapes)?")
print("   Bohr set B(Gamma,rho): Gamma = the large-spectrum freqs of 1_{mu_n} (the frequencies r with")
print("   |1_{mu_n}-hat(r)| = |f(r)| >= eta). t in B iff ||r t / p|| < rho for all r in Gamma.")
print(" n     p          avg|f|  M      #large-spec(eta=.5M)  |B|/p     mean|f| on b*+B   mean|f| on random+B")
for a_exp in range(3, 7):
    n = 2**a_exp
    beta = 4
    p, mu, h, F, a = build(n, beta)
    a0 = a.copy(); a0[0] = 0.0
    M = a0.max(); bstar = int(np.argmax(a0))
    avg = a0[a0 > 0].mean() if (a0 > 0).any() else 0.0
    # baseline avg of |f| over nonzero b (the L1 mean ~ the "bulk" level):
    avg_all = a0.mean()  # includes the b where |f| small; this is the bulk reference
    eta = 0.5 * M
    Gamma = [r for r in range(1, p) if a0[r] >= eta]      # large spectrum frequencies
    Gk = len(Gamma)
    # Bohr set B(Gamma, rho): for tractability cap |Gamma| and pick rho so |B| ~ moderate.
    rho = 0.1
    Gsub = Gamma[:min(Gk, 30)]
    def inB(t):
        for r in Gsub:
            v = (r * t) % p
            frac = min(v, p - v) / p
            if frac >= rho: return False
        return True
    # sample translates and measure |f| on b*+B vs random+B
    rs = np.random.RandomState(1)
    cand = rs.randint(1, p, size=20000)
    Bset = [int(t) for t in cand if inB(int(t))]
    Bfrac = len(Bset) / 20000.0
    if Bset:
        vals_star = np.array([a0[(bstar + t) % p] for t in Bset])
        rb = rs.randint(1, p)
        vals_rand = np.array([a0[(rb + t) % p] for t in Bset])
        ms, mr = vals_star.mean(), vals_rand.mean()
    else:
        ms = mr = float('nan')
    print(" %-4d  %-10d %-7.3f %-6.3f %-21d %-9.4f %-16.3f %-16.3f"
          % (n, p, avg_all, M, Gk, Bfrac, ms, mr))

# ---------------------------------------------------------------------------
# PART 3.  The structural verdict computation.  Croot-Sisask "2*avg" forcing requires
#   M <= 2 * avg.  We compute avg directly (the L1 mean of |f| over nonzero b) and the worst M and
#   report M / (2 avg).  If M / (2 avg) -> a constant <= 1 we'd have the floor; if it GROWS like
#   sqrt(log(p/n)), the almost-periodicity buys nothing past Johnson (the excess is unforced).
#   Also: avg|f| ~ ?  For a random-like subset of size n, E|f| ~ sqrt(n) (L1 of Gaussian); but the
#   FLOOR is sqrt(n log) so even 2*avg = 2 sqrt(n) is BELOW the floor when log(p/n) > 4 -> the
#   "2 avg" target, if achievable, would be STRONGER than the prize. Test whether M actually <= 2 avg.
# ---------------------------------------------------------------------------
print("\nPART 3 — does M <= 2*avg (the Croot-Sisask forcing target) hold, prize-faithfully?")
print(" n     p          avg|f|  M      M/(2 avg)   M/sqrt(n)   sqrt(2 ln(p/n))  Johnson=sqrt(n)?")
# vary beta too, to confirm the M/(2avg) growth tracks log(p/n) (the floor's excess), not n alone.
for a_exp, beta in [(3,4),(4,4),(5,4),(6,4),(4,5),(5,5),(5,6),(4,6)]:
    n = 2**a_exp
    p, mu, h, F, a = build(n, beta)
    a0 = a.copy(); a0[0] = 0.0
    M = a0.max()
    avg = a0.mean()  # L1 mean over all b!=0 (b=0 zeroed); this is the bulk average
    print(" %-4d  %-10d %-7.3f %-6.3f %-11.3f %-11.3f %-16.3f %s"
          % (n, p, avg, M, M/(2*avg), M/math.sqrt(n), math.sqrt(2*math.log(p/n)),
             "M>Johnson" if M > 1.05*math.sqrt(n) else "M~Johnson"))

print("\n" + "="*108)
print("READ: PART1 |T_1.0|/p tells if O(1) almost-periods are abundant (Croot-Sisask hypothesis).")
print("      PART2 mean|f| on b*+B vs random+B: if b*+B >> random+B the peak is a ROBUST PLATEAU")
print("            (almost-periodicity PRESERVES the peak, does NOT force it to avg) => NO forcing.")
print("      PART3 M/(2 avg): if it GROWS with n (tracks sqrt(log)), the 2*avg target is VIOLATED")
print("            => the floor's sqrt(log) excess is NOT captured by almost-periodicity.")
print("="*108)
