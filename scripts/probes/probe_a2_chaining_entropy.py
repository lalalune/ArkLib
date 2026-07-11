#!/usr/bin/env python3
"""
A2-CHAINING-ENTROPY probe (#444 prize, route 54).

NEW LEMMA UNDER TEST (relocate cancellation OFF the n-point domain, ONTO the
b-index process as a chaining/entropy functional):

  Let X_b = eta_b(mu_n) = sum_{x in mu_n} e_p(b x), b in F_p^* (the index set).
  M(mu_n) = max_b |X_b| is the supremum of this (deterministic) process.
  Generic chaining (Talagrand) bounds the sup of a sub-Gaussian process by
  the gamma_2 functional = integral of sqrt(log N(T, d, eps)) over scales eps,
  where N is the covering number of the index (T = F_p^*) under the canonical
  L^2 increment metric d(b,b') = (avg_? |X_b - X_b'|^2)^{1/2}.

  Plain chaining over q points gives sqrt(log q) per scale ~= the WALL (W4).
  The lemma CLAIMS: the 2-adic dilation self-similarity (X_b and X_{zeta b}
  are tied by the tower recursion X_b(G_{i+1}) = X_b(G_i) + X_{zeta b}(G_i))
  makes the metric entropy log N(eps) GROW LIKE o(log q) -- i.e. the index
  collapses onto a low-entropy (self-similar/dilation-orbit) structure, so the
  gamma_2 functional absorbs the sqrt(log) excess and yields M <= C sqrt(n log).

HOW WE TEST IT (honestly, no randomness; M is a deterministic max):
  1. Build the increment metric on the index. The natural metric for THIS
     process: d(b,b')^2 = |X_b - X_b'|^2 is degenerate (depends on the single
     fixed mu_n). The RIGHT chaining metric is the one that makes X sub-Gaussian
     w.r.t. it. For a Gauss-sum process indexed by b, treat the "ensemble" as
     b ranging and measure the empirical covering numbers N(eps) of the value
     map b -> X_b in C, at geometric scales eps_k = sqrt(n)*2^{-k}.
  2. Compute log N(eps_k) and form the chaining sum
        gamma_2_emp = sum_k eps_k * sqrt(log N(eps_k))   (Dudley/Talagrand form)
     and compare its leading order to sqrt(n log q) (floor) vs n (trivial)
     vs sqrt(n)*log q (plain-chaining wall would give sqrt(n log q)*something).
  3. CRUCIAL self-similarity test: does N(eps) for the FULL index F_p^* equal
     (up to the dilation-orbit factor n) the covering number of a single
     dilation-orbit class? If the index quotients by the n-element dilation
     orbit b ~ zeta b ~ ... and the quotient has SMALL covering numbers,
     entropy is o(log q). If the quotient still has ~q/n points with full
     spread, entropy is Theta(log q) = WALL.

PROPER REGIME: p PRIME, n=2^mu, n | p-1, p >> n^3, proper subgroup (NEVER n=p-1).
"""
import cmath, math, sys

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % m == 0: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def find_prime(mu, beta):
    """smallest prime p > n^beta with n | p-1, n=2^mu, proper subgroup."""
    n = 1 << mu
    lo = int(n**beta)
    t = ((lo // n) + 1) * n + 1
    while True:
        if isprime(t):
            return n, t
        t += n

def subgroup(p, n):
    """generator h of the order-n subgroup; returns list of its elements."""
    # find primitive root
    fac = []; x = p-1; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    g = None
    for c in range(2, p):
        if all(pow(c, (p-1)//q, p) != 1 for q in fac):
            g = c; break
    h = pow(g, (p-1)//n, p)
    H = [pow(h, i, p) for i in range(n)]
    assert len(set(H)) == n and pow(h, n//2, p) != 1, "not proper order-n"
    return h, H

def eta(b, H, p):
    w = 2*math.pi/p
    s = 0j
    for x in H:
        s += cmath.exp(1j*w*((b*x) % p))
    return s

def covering_number(values, eps):
    """greedy eps-net covering number of points (complex) under |.| metric."""
    centers = []
    for v in values:
        if all(abs(v - c) > eps for c in centers):
            centers.append(v)
    return len(centers)

def main():
    print("A2-CHAINING-ENTROPY: covering-number/metric-entropy of b->X_b process")
    print("Q: log N(eps) ~ log q (WALL) or o(log q) (FLOOR via dilation self-similarity)?")
    print(f"{'mu':>3}{'n':>5}{'p':>9}{'beta':>6}  {'M':>7}{'floor':>7}{'M/fl':>6}"
          f"  {'g2_emp':>8}{'sqrt(nlogq)':>11}{'g2/fl':>7}  {'logN(.5sqrtn)':>13}{'logq':>6}{'ratio':>6}")
    for mu, beta in [(2,3.2),(3,3.2),(4,3.2),(5,3.2),(6,3.2),(7,3.2)]:
        n, p = find_prime(mu, beta)
        h, H = subgroup(p, n)
        # full index F_p^*  (cap to keep runtime sane at large p: sample uniformly)
        # but covering numbers need the TRUE distribution -> use all of F_p^* when small,
        # else a dense uniform stride (deterministic, no RNG).
        if p <= 200000:
            bs = range(1, p)
        else:
            stride = max(1, (p-1)//200000)
            bs = range(1, p, stride)
        vals = [eta(b, H, p) for b in bs]
        M = max(abs(v) for v in vals)
        floor = math.sqrt(n*math.log(p/n))
        logq = math.log(p)
        # chaining sum over geometric scales
        g2 = 0.0
        scales = []
        k = 0
        eps0 = math.sqrt(n)
        # only sample a manageable number of scales; covering number is O(len(vals)^2)
        # so subsample vals for the net computation while keeping spread
        netvals = vals if len(vals) <= 4000 else vals[::max(1, len(vals)//4000)]
        logN_half = None
        while True:
            eps = eps0 * (2**(-k))
            if eps < 0.05*eps0/ (2**5):  # ~ down to fine scale
                break
            N = covering_number(netvals, eps)
            lN = math.log(N)
            # Dudley: integral ~ sum (eps_{k}-eps_{k+1}) sqrt(log N(eps_k)) ~ eps_k * sqrt(logN)
            g2 += eps * math.sqrt(max(lN, 0.0))
            if abs(eps - 0.5*eps0) < 0.26*eps0 and logN_half is None:
                logN_half = lN
            k += 1
            if k > 20: break
        if logN_half is None:
            logN_half = math.log(covering_number(netvals, 0.5*eps0))
        ratio_entropy = logN_half / logq if logq > 0 else float('nan')
        print(f"{mu:>3}{n:>5}{p:>9}{beta:>6.1f}  {M:>7.2f}{floor:>7.2f}{M/floor:>6.2f}"
              f"  {g2:>8.2f}{math.sqrt(n*logq):>11.2f}{g2/floor:>7.2f}"
              f"  {logN_half:>13.2f}{logq:>6.2f}{ratio_entropy:>6.2f}")
    print()
    print("READING:")
    print(" - If logN(.5sqrtn)/logq -> a CONSTANT < 1 that SHRINKS with mu => entropy o(log q): FLOOR.")
    print(" - If logN/logq stays ~ const (Theta(1)) i.e. logN ~ Theta(log q): plain chaining = WALL.")
    print(" - g2_emp/floor near a constant independent of mu,p would be the floor signature.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
