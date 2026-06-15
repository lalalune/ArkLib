#!/usr/bin/env python3
"""
#407 prize-regime CRACK test (c.188 gating driver = v2(p-1), not beta).

Claim to test: M(n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)| is TAMER for primes with
v2(p-1) = mu EXACTLY (index m=(p-1)/n ODD) than for v2(p-1) > mu (m even). If the prize
designer can CHOOSE q with v2(q-1)=mu and that bucket keeps M/sqrt(n log(p/n)) bounded,
that is a CRACK TOWARD CLOSURE (not refutation): the floor could hold for the chosen field.

Method: indicator of mu_n in Z/p, real FFT, max magnitude over nonzero freqs = M(n) exactly.
Bucket primes by t := v2(p-1) - mu (t=0 => m odd). Report ratio R = M / sqrt(n log(p/n)).
"""
import numpy as np
from sympy import isprime

def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def mu_n_indicator_max(p, n):
    # generator g of F_p^*; mu_n = { g^{(p-1)/n * j} } = the unique subgroup of order n
    # find a generator (primitive root) the cheap way for moderate p
    # subgroup of order n = n-th powers' ... actually mu_n = {x : x^n = 1}.
    # build it directly: find an element of order n.
    # element of order n: take h = g^{(p-1)/n}; we need a primitive root g.
    g = primitive_root(p)
    step = (p - 1) // n
    h = pow(g, step, p)
    # mu_n = {h^j mod p : j in 0..n-1}
    elts = set()
    cur = 1
    for _ in range(n):
        elts.add(cur)
        cur = (cur * h) % p
    assert len(elts) == n, (p, n, len(elts))
    ind = np.zeros(p, dtype=np.float64)
    for e in elts:
        ind[e] = 1.0
    F = np.fft.rfft(ind)            # DFT_b = sum_x ind[x] e^{-2pi i b x / p} = sum_{x in mu_n} e_p(-b x)
    mag = np.abs(F)
    mag[0] = -1.0                   # exclude b=0 (that's |mu_n| = n)
    return mag.max()

def primitive_root(p):
    # factor p-1
    fac = factorize(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primroot")

def factorize(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

def primes_for(n, count_per_bucket=6, pmax=2_000_000):
    """find primes p ≡ 1 mod n, bucketed by t = v2(p-1)-mu (mu=log2 n)."""
    mu = n.bit_length() - 1
    buckets = {}
    p = n + 1
    while p < pmax:
        if p % n == 1 and isprime(p):
            t = v2(p - 1) - mu
            buckets.setdefault(t, [])
            if len(buckets[t]) < count_per_bucket:
                buckets[t].append(p)
        p += n
        if all(len(buckets.get(t, [])) >= count_per_bucket for t in (0, 1, 2)):
            break
    return mu, buckets

print(f"{'n':>4} {'t=v2-mu':>8} {'p':>10} {'m=(p-1)/n':>12} {'M(n)':>9} {'R=M/sqrt(n ln(p/n))':>22}")
print("-" * 75)
summary = {}
for n in [8, 16, 32, 64, 128]:
    mu, buckets = primes_for(n)
    for t in sorted(buckets):
        if t > 3: continue
        Rs = []
        for p in buckets[t]:
            M = mu_n_indicator_max(p, n)
            R = M / np.sqrt(n * np.log(p / n))
            Rs.append(R)
            print(f"{n:>4} {t:>8} {p:>10} {(p-1)//n:>12} {M:>9.2f} {R:>22.4f}")
        summary.setdefault(t, []).append((n, np.mean(Rs), np.max(Rs)))
    print()

print("=== SUMMARY: mean/max R by bucket t=v2(p-1)-mu (t=0 => m ODD = prize-choosable) ===")
for t in sorted(summary):
    print(f"  t={t}: " + ", ".join(f"n={n}:mean{m:.3f}/max{mx:.3f}" for n, m, mx in summary[t]))
print("\nCRACK if t=0 (odd m) bucket R stays bounded/flat while t>=1 grows with n.")
print("REFUTES the crack if t=0 R also grows with n (then odd-m doesn't tame M).")
