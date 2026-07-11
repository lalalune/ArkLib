#!/usr/bin/env python3
"""I031 orbit-invariance — the EXACT COMPLEX strengthening (formalized in
ArkLib/.../Frontier/I031DilationOrbitReduction.lean).

The committed `probe_i031_orbit_invariance.py` checks |eta(h*b)| == |eta(b)| for h a
*generator* of mu_n. The Lean brick proves the STRONGER pointwise complex equality
  eta(zeta*b) == eta(b)   for EVERY zeta in mu_n (not just the generator, and the complex
value, not just its modulus),
because mu_n = nthRootsFinset n 1 is closed under multiplication by any of its own elements
(dilate zeta mu_n = mu_n), so eta_dilate forces eta(zeta*b) = eta_b(zeta . mu_n) = eta_b(mu_n).

This probe validates that exact complex equality at prize-regime primes BEFORE relying on the
Lean theorem, per the probe-first contract. PROPER subgroup mu_n (n=2^a), p >> n^3, n | p-1,
NEVER n=q-1. Verdict: max |eta(zeta*b) - eta(b)| over ALL zeta in mu_n is machine-epsilon.
"""
import cmath, math, random

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % m == 0: continue
        x = pow(a, d, m)
        if x == 1 or x == m - 1: continue
        ok = False
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1: ok = True; break
        if not ok: return False
    return True

def find_prime(mu, beta):
    n = 1 << mu; lo = int(n ** beta); t = ((lo // n) + 1) * n + 1
    while True:
        if isprime(t): return n, t
        t += n

def subgroup(p, n):
    fac = []; x = p - 1; d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for c in range(2, p):
        if all(pow(c, (p - 1) // q, p) != 1 for q in fac): g = c; break
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    assert len(set(H)) == n and pow(h, n // 2, p) != 1   # PROPER, thin 2-power
    return h, H

print("I031 EXACT COMPLEX orbit-invariance  eta(zeta*b) == eta(b)  for ALL zeta in mu_n")
print(f"{'n':>4} {'p':>10} {'m=(p-1)/n':>10}  max|eta(zeta b)-eta(b)| over ALL zeta in mu_n")
random.seed(31)
for mu, beta in [(2,3.2),(3,3.2),(4,3.2),(5,3.2)]:
    n, p = find_prime(mu, beta)
    h, H = subgroup(p, n)
    w = 2 * math.pi / p
    def eta(b): return sum(cmath.exp(1j * w * ((b * x) % p)) for x in H)
    md = 0.0
    for _ in range(30):
        b = random.randrange(1, p)
        eb = eta(b)
        for zeta in H:                       # EVERY element of mu_n, not just the generator
            md = max(md, abs(eta((zeta * b) % p) - eb))
    m = (p - 1) // n
    print(f"{n:>4} {p:>10} {m:>10}  {md:.2e}")
print("\nVERDICT: exact complex equality (machine epsilon) for every zeta in mu_n => sup over Fp* "
      "collapses to sup over m=(p-1)/n orbit reps (log p -> log(p/n)).")
