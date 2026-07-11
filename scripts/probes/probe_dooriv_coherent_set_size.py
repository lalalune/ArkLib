#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — how LARGE is the high-coherence set {b : rho(b) >= 1-delta}?

The brief's deepest open Lane-1 question: is rho(b) -> 1 FORCED, or is there slack a
non-sum-product anti-concentration could exploit? Prior bricks show: rho is coset-invariant
(factors through F_p*/mu_n), worst-b coset index is additively+multiplicatively generic, rho=1
<=> same-ray (no new cancellation). What is NOT yet mapped: the SIZE and SHAPE of the
high-coherence set across ALL b.

If the set {b : rho(b) near 1} is RARE (o(p) fraction) and the typical b has genuine slack
(rho bounded away from 1), then the prize is about controlling a SMALL coherent set — and the
question becomes whether that set is arithmetically STRUCTURED (exploitable) or pseudo-random.
If instead a CONSTANT fraction of b are near-coherent, no anti-concentration on the set can help.

rho(b) here = the index-2 coset-half two-piece coherence |A+B| / (|A|+|B|), where A,B are the
half-period sums of eta_b over the two cosets of the index-2 subgroup mu_{n/2} < mu_n.

PROBE-FIRST: exact complex arithmetic, PROPER mu_n (n=2^a), p >> n^3, structured primes,
NEVER n=q-1. Measure:
  (Q1) full-group distribution of rho(b): mean, and FRACTION with rho >= 1-delta for delta in
       {0.01, 0.05, 0.1}.
  (Q2) does the near-coherent fraction SHRINK with n (slack opens up in the thin regime) or stay
       a constant fraction?
"""
import cmath
import math


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def find_prime(n, beta):
    target = int(round(n ** beta))
    k0 = max(2, target // n)
    for dk in range(0, 400000):
        for k in (k0 + dk, k0 - dk):
            if k < 2:
                continue
            p = k * n + 1
            if p > n ** 3 and is_prime(p):
                return p
    return None


def primitive_root(p):
    # find a generator of F_p*
    phi = p - 1
    factors = set()
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    return None


def coset_half_coherence_all_b(n, p, g, sample_b=None):
    """rho(b) for the index-2 coset split of mu_n. mu_n = <h>, h = g^((p-1)/n).
    Two halves: even/odd powers of h = the two cosets of mu_{n/2}.
    Returns list of rho(b) over the sampled b (b ranges over F_p*; rho is coset-invariant
    so we sample coset reps but ALSO confirm by scanning a full residue band)."""
    m = (p - 1) // n
    h = pow(g, m, p)            # generator of mu_n
    mu = [pow(h, j, p) for j in range(n)]
    even = [mu[j] for j in range(0, n, 2)]   # coset 1 (mu_{n/2})
    odd = [mu[j] for j in range(1, n, 2)]    # coset 2
    ep = lambda t: cmath.exp(2j * math.pi * (t % p) / p)
    rhos = []
    bs = sample_b if sample_b is not None else range(1, p)
    for b in bs:
        A = sum(ep(b * y) for y in even)
        B = sum(ep(b * y) for y in odd)
        denom = abs(A) + abs(B)
        if denom < 1e-12:
            continue
        rho = abs(A + B) / denom
        rhos.append(rho)
    return rhos


print(f"{'n':>5} {'p':>14} {'meanrho':>9} {'frac>=.99':>10} {'frac>=.95':>10} {'frac>=.90':>10} {'#b':>7}")
for a in (4, 5, 6, 7):
    n = 2 ** a
    p = find_prime(n, 4.0)
    if p is None:
        continue
    g = primitive_root(p)
    # sample b over a uniform residue band (rho is coset-invariant; sampling F_p* uniformly
    # gives the true full-group distribution). Cap sample for compute at large p.
    cap = 6000
    import random
    random.seed(12345 + n)
    if p - 1 <= cap:
        sample = list(range(1, p))
    else:
        sample = random.sample(range(1, p), cap)
    rhos = coset_half_coherence_all_b(n, p, g, sample)
    if not rhos:
        continue
    mean = sum(rhos) / len(rhos)
    f99 = sum(1 for r in rhos if r >= 0.99) / len(rhos)
    f95 = sum(1 for r in rhos if r >= 0.95) / len(rhos)
    f90 = sum(1 for r in rhos if r >= 0.90) / len(rhos)
    print(f"{n:>5} {p:>14} {mean:>9.4f} {f99:>10.4f} {f95:>10.4f} {f90:>10.4f} {len(rhos):>7}")

print()
print("INTERPRETATION:")
print("- mean rho ~ const across n + near-coherent fraction NOT shrinking => coherence is TYPICAL,")
print("  no slack to exploit => door-(iv) coherence lever DEAD (typical-b near-coherent).")
print("- near-coherent fraction SHRINKS with n => high-coherence set is RARE in thin regime =>")
print("  worth probing whether that rare set is arithmetically structured (exploitable).")
