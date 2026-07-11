#!/usr/bin/env python3
"""
A2 self-similarity CRUX test (#444, route 54).

The route-54 lemma REQUIRES the 2-adic dilation orbit b ~ zeta b ~ ... ~ zeta^{n-1} b
to COLLAPSE the index metric: i.e. b and zeta b must be CLOSE under the canonical
chaining metric d, so the q points of F_p^* quotient onto ~ q/n (or fewer) effective
classes, dropping the entropy below log q.

DIRECT TEST: measure d(b, zeta b) for the d-metric d^2(c) = (2/n) sum_{x in mu_n}
(1 - cos(2pi c x / p)). Note X_{zeta b} appears in the tower recursion; if the
relocation worked, dilation neighbors would be metrically close (small d), giving the
entropy collapse.

We report, over random b:
  - the d-distance d(b, zeta b) (dilation neighbor) vs the GLOBAL average d(b,b')
  - whether dilation neighbors are SYSTEMATICALLY closer (collapse) or generic (no collapse)
  - the diameter and the typical distance, to see how much of F_p is at near-max distance.

PROPER REGIME: p PRIME, n=2^mu, n | p-1, p >> n^3, proper subgroup.
"""
import math, sys, random

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
    random.seed(12345)  # deterministic
    print("A2 DILATION-COLLAPSE crux: is d(b, zeta*b) << typical d(b,b')? (needed for entropy collapse)")
    print(f"{'mu':>3}{'n':>5}{'p':>10}  {'diam':>6}{'avg_d':>7}{'d(b,zb)':>9}{'med d(b,zb)':>12}"
          f"  {'collapse?':>10}")
    for mu, beta in [(3,3.2),(4,3.2),(5,3.2),(6,3.2),(7,3.2)]:
        n, p = find_prime(mu, beta)
        h, H = subgroup(p, n)
        zeta = h  # primitive n-th root = the dilation generator
        w = 2*math.pi/p
        def d2(c):
            c %= p
            s = 0.0
            for x in H:
                s += 1 - math.cos(w * ((c*x) % p))
            return max(2.0*s/n, 0.0)
        def d(b, bp):
            return math.sqrt(d2((b - bp) % p))
        # diameter: max over a sample of c
        samp = [random.randrange(1, p) for _ in range(300)]
        diam = max(math.sqrt(d2(c)) for c in samp)
        # typical d(b,b') over random pairs
        avg_d = sum(math.sqrt(d2((random.randrange(1,p)-random.randrange(1,p))%p)) for _ in range(400))/400
        # dilation neighbor distances d(b, zeta*b)
        dz = []
        for _ in range(400):
            b = random.randrange(1, p)
            dz.append(d(b, (zeta*b) % p))
        dz.sort()
        avg_dz = sum(dz)/len(dz)
        med_dz = dz[len(dz)//2]
        collapse = avg_dz < 0.5*avg_d
        print(f"{mu:>3}{n:>5}{p:>10}  {diam:>6.3f}{avg_d:>7.3f}{avg_dz:>9.3f}{med_dz:>12.3f}"
              f"  {str(collapse):>10}")
    print()
    print("If d(b, zeta*b) ~ avg_d (NOT smaller) => dilation neighbors are metrically GENERIC =>")
    print("the orbit does NOT collapse the index => entropy stays Theta(log q) = the WALL.")
    print("(For the relocation to work we'd need d(b,zeta*b) -> 0, i.e. systematic closeness.)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
