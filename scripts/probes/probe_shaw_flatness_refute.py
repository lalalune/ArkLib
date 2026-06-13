#!/usr/bin/env python3
"""
probe_shaw_flatness_refute.py  (#389/#371)

REFUTES the 'Shaw Flatness' constant: B(mu_n) = max_{b!=0}|eta_b| is NOT <= sqrt(2*n).
  eta_b = sum_{x in mu_n} exp(2*pi*i*b*x/p);  eta_b is constant on the (p-1)/n ~ q/n mu_n-cosets,
  so we evaluate one b per coset (g^i, i<(p-1)/n) for speed.

MEASURED: B = Theta(sqrt(n*log2(q/n)))  with constant ~1.0  (B/sqrt(n*log2(q/n)) in [0.80,1.21]
across n=8,16,32 and log2(q/n)=3..12).  So B/sqrt(n) GROWS like sqrt(log2(q/n)); there is NO
constant-times-sqrt(n) flatness with constant sqrt(2).  For the PRIZE, q/n ~ 1/eps* = 2^128
(constant in n), so B ~ sqrt(128)*sqrt(n) ~ 11.3*sqrt(n) -- 8x the sqrt(2) bound.

Consequence: the correct flatness constant is sqrt(log2(1/eps*)), NOT sqrt(2); any closed-form
delta* derived from B <= sqrt(2)*sqrt(n) must be re-derived with B ~ sqrt(n*log(q/n)).  The
Shaw-operator UNIFICATION (incidence = average + Shaw error) is unaffected; only the load-bearing
flatness *constant* is corrected.  The surviving sqrt(log) factor is the genuine W4 (worst-case
incomplete-character-sum / Bourgain-regime) content of the prize.
"""
import cmath, math

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True

def B_of(p, n):
    def order(a):
        x = a % p; o = 1
        while x != 1: x = (x * a) % p; o += 1
        return o
    g = next(c for c in range(2, p) if order(c) == p - 1)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, j, p) for j in range(n)]
    W = [cmath.exp(2j * math.pi * k / p) for k in range(p)]
    ncos = (p - 1) // n
    best = 0.0; rep = 1
    for _ in range(ncos):
        s = abs(sum(W[(rep * x) % p] for x in mu))
        if s > best: best = s
        rep = (rep * g) % p
    return best

def prime_near(n, target):
    t = max(2, target // n)
    for dt in range(0, 5000):
        for tt in (t + dt, t - dt):
            if tt > 1 and is_prime(n * tt + 1): return n * tt + 1
    return None

if __name__ == "__main__":
    print(f"{'n':>4} {'p':>8} {'log2(q/n)':>9} {'B':>8} {'B/sqrt(n)':>10} {'B/sqrt(n*log2(q/n))':>20}")
    for n in (8, 16, 32):
        for target in (300, 3000, 30000):
            p = prime_near(n, target)
            if p and p < 60000:
                B = B_of(p, n); l = math.log2((p - 1) / n)
                print(f"{n:>4} {p:>8} {l:>9.2f} {B:>8.3f} {B/math.sqrt(n):>10.3f} "
                      f"{B/math.sqrt(n*l):>20.3f}")
