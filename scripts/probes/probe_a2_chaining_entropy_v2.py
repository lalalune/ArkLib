#!/usr/bin/env python3
"""
A2-CHAINING-ENTROPY v2 (#444, route 54) -- the HONEST index-metric version.

v1 measured the covering number of the VALUE cloud {X_b} in C, which is trivially
O(log) because the values live in a 2D disk of radius ~ sqrt(n log q). That is a
FALSE floor signal (it has nothing to do with the index process).

The correct chaining functional needs the covering number of the INDEX set
T = F_p^* under the CANONICAL increment metric of the process. For the Gauss-sum
process X_b = sum_{x in mu_n} psi(b x), the canonical sub-Gaussian metric is

    d(b,b')^2 := (1/n) * sum_{x in mu_n} |psi(b x) - psi(b' x)|^2
               = (2/n) * sum_{x in mu_n} (1 - cos(2pi (b-b') x / p)).

This is the metric under which X_b is sub-Gaussian (X_b is a sum of n unit phasors
indexed by x; the increment X_b - X_b' = sum_x (psi(bx)-psi(b'x)) has variance-proxy
n * d(b,b')^2, and each summand is bounded, so Hoeffding/Azuma => sub-Gaussian
w.r.t. this d up to the constant). NOTE: d depends only on c = b - b' and on mu_n.

THEN generic chaining (Dudley) gives:
    M = max_b |X_b| <~ sqrt(n) * gamma_2,
    gamma_2 = integral_0^{diam} sqrt(log N(T, d, eps)) d eps  (in d-units, diam = O(1)).

NEW LEMMA (route 54): the 2-adic dilation self-similarity makes
    log N(T, d, eps) = o(log q)  uniformly in eps,
so gamma_2 = o(sqrt(log q)) and M = o(sqrt(n log q))... wait, that would BEAT the
floor, which is impossible (the floor sqrt(n log q) is a LOWER bound too). So the
HONEST target is: gamma_2 = Theta(sqrt(log q)) gives EXACTLY the floor, and the
lemma must show gamma_2 <= C sqrt(log(q/n)) (NOT o, but the right CONSTANT/scale),
matching M <= C sqrt(n log(q/n)). The wall would be gamma_2 ~ sqrt(log q) * (extra),
or the chaining being LOOSE (sup >> gamma_2).

WHAT WE ACTUALLY TEST:
  (1) Compute the TRUE covering number N(T, d, eps) of the index under d, at scales.
  (2) Compute gamma_2 (Dudley sum) and compare M to sqrt(n)*gamma_2: is chaining
      TIGHT (M ~ sqrt(n) gamma_2, then the floor is exactly the entropy integral)
      or LOOSE (M << sqrt(n) gamma_2 => the dilation structure is NOT captured by d,
      OR M >> meaning d-metric is wrong)?
  (3) The decisive self-similarity test: log N(T,d,eps) vs log q. Does the dilation
      orbit b ~ zeta b COLLAPSE the index (small N) or not?

PROPER REGIME: p PRIME, n=2^mu, n | p-1, p >> n^3, proper subgroup.
"""
import cmath, math, sys

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m-1; s = 0
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
    n = 1 << mu
    lo = int(n**beta)
    t = ((lo // n) + 1) * n + 1
    while True:
        if isprime(t): return n, t
        t += n

def subgroup(p, n):
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
    assert len(set(H)) == n and pow(h, n//2, p) != 1
    return h, H

def main():
    print("A2-CHAINING-ENTROPY v2: TRUE index metric d(b,b')^2 = (2/n) sum_x (1-cos(2pi(b-b')x/p))")
    print("Chaining: M <~ sqrt(n)*gamma_2.  Floor needs gamma_2 = Theta(sqrt(log(q/n))).")
    print(f"{'mu':>3}{'n':>5}{'p':>10}  {'M':>7}{'floor':>7}{'M/fl':>6}"
          f"  {'g2':>6}{'sqrtLog':>8}{'sqrtn*g2':>9}{'M/(sqn g2)':>11}"
          f"  {'maxlogN':>8}{'logq':>6}{'mxlN/lq':>8}")
    for mu, beta in [(2,3.2),(3,3.2),(4,3.2),(5,3.2),(6,3.2),(7,3.2)]:
        n, p = find_prime(mu, beta)
        h, H = subgroup(p, n)
        w = 2*math.pi/p
        # M and X_b: index over F_p^* (sample if huge, deterministic stride)
        if p <= 300000:
            bs = list(range(1, p))
        else:
            stride = max(1, (p-1)//300000)
            bs = list(range(1, p, stride))
        def Xb(b):
            return sum(cmath.exp(1j*w*((b*x) % p)) for x in H)
        M = max(abs(Xb(b)) for b in bs)
        floor = math.sqrt(n*math.log(p/n))
        logq = math.log(p)
        # d-metric depends only on c=b-b'. Precompute d(0,c)=metric of difference c.
        # d^2(c) = (2/n) sum_x (1 - cos(w * c * x)). Center b'=0 sense: actually need
        # pairwise, but d(b,b') = d-function of (b-b') => the metric is TRANSLATION-INV
        # on the additive group F_p. So covering F_p under d == covering by the level
        # sets of the single function rho(c) = d(0,c). The covering number N(eps) =
        # number of eps-separated points = (size of F_p) / (size of eps-ball under rho).
        # eps-ball B(0,eps) = { c : rho(c) <= eps }. Translation-invariance => all balls
        # same size => N(eps) ~ p / |B(0,eps)| (packing/covering up to factor).
        def rho(c):
            s = 0.0
            for x in H:
                s += 1 - math.cos(w * ((c*x) % p))
            return math.sqrt(max(2.0*s/n, 0.0))
        # rho is bounded by 2 (since each term <=2, avg <=2 => rho<=2). diam ~ 2.
        # compute |B(0,eps)| over a sample of c (deterministic stride), scale up.
        if p <= 300000:
            cs = list(range(1, p))
            sample_factor = 1.0
        else:
            stride = max(1, (p-1)//300000)
            cs = list(range(1, p, stride))
            sample_factor = (p-1)/len(cs)
        rhos = [rho(c) for c in cs]
        diam = max(rhos)
        # Dudley sum over geometric scales in d-units
        # gamma_2 = sum_k (eps_k - eps_{k+1}) sqrt(log N(eps_k)), eps_k = diam * 2^{-k}
        # N(eps) = p / (sample_factor * #{c : rho(c) <= eps})  (covering ~ packing)
        g2 = 0.0
        maxlogN = 0.0
        K = 16
        prev_eps = diam
        for k in range(0, K):
            eps = diam * (2**(-k))
            ball = sum(1 for r in rhos if r <= eps) * sample_factor + 1  # +1 for c=0
            N = max((p) / ball, 1.0)
            lN = math.log(N)
            maxlogN = max(maxlogN, lN)
            de = prev_eps - eps
            g2 += de * math.sqrt(max(lN, 0.0))
            prev_eps = eps
        sqrtLog = math.sqrt(math.log(p/n))
        print(f"{mu:>3}{n:>5}{p:>10}  {M:>7.2f}{floor:>7.2f}{M/floor:>6.2f}"
              f"  {g2:>6.2f}{sqrtLog:>8.2f}{math.sqrt(n)*g2:>9.2f}{M/(math.sqrt(n)*g2):>11.2f}"
              f"  {maxlogN:>8.2f}{logq:>6.2f}{maxlogN/logq:>8.2f}")
    print()
    print("READING:")
    print(" maxlogN/logq -> if it STAYS ~ const Theta(1) => log N = Theta(log q): chaining over")
    print("   the index needs the FULL sqrt(log q) => plain chaining = the WALL (no relocation).")
    print(" If maxlogN/logq SHRINKS to 0 with q => entropy o(log q): the dilation collapses the")
    print("   index and the floor is reachable from entropy (the CRACK).")
    print(" M/(sqrt(n) g2): chaining tightness. If ~ Theta(1) the floor IS the entropy integral.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
