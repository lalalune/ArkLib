#!/usr/bin/env python3
"""
Probe for the S11 MGF rate-monotonicity brick.

For proper thin 2-power subgroups mu_n in F_p, compute the normalized period spectrum
  t_b = |sum_{x in mu_n} exp(2*pi*i*b*x/p)|^2 / n
(one representative per b in F_p^*) and verify empirically that the MGF is monotone in the
rate parameter c: c' <= c => mean(exp(c' t_b)) <= mean(exp(c t_b)).

This is the numerical sanity check for the formal pointwise theorem: t_b >= 0, so exp(c' t_b) <=
exp(c t_b). It never tests the full group n=p-1.
"""
import cmath
import math

CONFIGS = [
    (16, 65537),   # Fermat, proper thin-ish, p >> n^3
    (32, 786433),  # p = 1 mod 32, p >> n^3
]
RATES = [0.10, 0.25, 0.50, 0.75]

def subgroup_mu(n, p):
    # find primitive-ish generator by brute force enough for these primes
    factors = set()
    m = p - 1
    d = 2
    mm = m
    while d * d <= mm:
        if mm % d == 0:
            factors.add(d)
            while mm % d == 0:
                mm //= d
        d += 1
    if mm > 1:
        factors.add(mm)
    g = None
    for cand in range(2, p):
        if all(pow(cand, (p - 1) // q, p) != 1 for q in factors):
            g = cand
            break
    assert g is not None
    step = pow(g, (p - 1) // n, p)
    xs = []
    v = 1
    for _ in range(n):
        xs.append(v)
        v = (v * step) % p
    assert len(set(xs)) == n and n < p - 1
    return xs

def spectrum_t(n, p):
    xs = subgroup_mu(n, p)
    twopi = 2.0 * math.pi
    vals = []
    for b in range(1, p):
        z = sum(cmath.exp(1j * twopi * ((b * x) % p) / p) for x in xs)
        vals.append((z.real * z.real + z.imag * z.imag) / n)
    return vals

def mgf(vals, c):
    return sum(math.exp(c * t) for t in vals) / len(vals)

for n, p in CONFIGS:
    vals = spectrum_t(n, p)
    print(f"n={n} p={p} proper={(p-1)//n >= 2} min_t={min(vals):.6g} max_t={max(vals):.6g}")
    prev = None
    for c in RATES:
        m = mgf(vals, c)
        print(f"  c={c:.2f} MGF={m:.12g}")
        if prev is not None and m + 1e-10 < prev:
            raise SystemExit(f"FAIL: MGF decreased from {prev} to {m}")
        prev = m
print("PASS: empirical MGF is monotone increasing in c on proper thin mu_n spectra")
