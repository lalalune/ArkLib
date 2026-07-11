#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the EXACT factorization |eta_b| = rho(b) * (|A|+|B|) and where the prize lives.

By DEFINITION of the index-2 coset-half coherence rho(b) = |A+B| / (|A|+|B|) (A,B = half-period
sums over the two cosets of mu_{n/2}<mu_n, A+B = eta_b), we have the EXACT identity
    |eta_b| = rho(b) * (|A| + |B|).
So the prize size is COHERENCE times HALF-MASS. My prior brick (coherence-slack-vacuous-at-argmax)
showed rho(b*)=1 at the prize-worst b*. Hence at the worst-b, |eta_{b*}| = |A|+|B| EXACTLY: the prize
peak is the FULL half-mass, undamped by coherence.

This probe asks the consequent localization question: with coherence pinned at 1 at b*, the entire
prize burden moves onto the HALF-MASS L1 = |A|+|B|. Does the half-mass itself have a sqrt(n)-shaped
ceiling, or is IT where the n^{1-o(1)} excess lives? Probe:
  (Q1) confirm the identity |eta_b| = rho(b)*(|A|+|B|) to machine precision (sanity).
  (Q2) at the prize-worst b*, report |A|+|B| / sqrt(n) and confirm it equals |eta_{b*}|/sqrt(n)
       (i.e. rho=1 => half-mass IS the peak).
  (Q3) max over b of (|A|+|B|)/sqrt(n): is the half-mass L1 bounded like the period (worst ~ a few
       sqrt(n)) or does it blow up? If the half-mass has the SAME sqrt(n*log) wall, the factorization
       just RELOCATES the wall (honest: no escape). If the half-mass is provably O(sqrt n) while the
       period isn't, that would be a real lever (almost certainly NOT — but probe-first).

EXACT setup: PROPER mu_n (n=2^a), p>>n^3, structured primes, never n=q-1. n=16 FULL F_p* scan.
"""
import cmath
import math
import random


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


def halves(n, p, g):
    m = (p - 1) // n
    h = pow(g, m, p)
    mu = [pow(h, j, p) for j in range(n)]
    even = [mu[j] for j in range(0, n, 2)]
    odd = [mu[j] for j in range(1, n, 2)]
    return even, odd


print(f"{'n':>5} {'p':>11} {'identity_maxerr':>15} {'|eta(b*)|/sqn':>13} {'halfmass(b*)/sqn':>17} "
      f"{'max_halfmass/sqn':>17} {'max|eta|/sqn':>13} {'mode':>10}")
for a, full in ((4, True), (5, False), (6, False)):
    n = 2 ** a
    p = find_prime(n, 4.0)
    g = primitive_root(p)
    even, odd = halves(n, p, g)
    sqn = math.sqrt(n)
    tau = 2.0 * math.pi / p
    if full:
        bs = range(1, p)
    else:
        random.seed(99 + n)
        bs = random.sample(range(1, p), min(6000, p - 1))
    id_err = 0.0
    best_eta = (-1.0, 0.0)      # (|eta|/sqn, halfmass/sqn at that b)
    max_half = 0.0
    max_eta = 0.0
    for b in bs:
        A = sum(cmath.exp(1j * tau * ((b * y) % p)) for y in even)
        B = sum(cmath.exp(1j * tau * ((b * y) % p)) for y in odd)
        eta = abs(A + B)
        half = abs(A) + abs(B)
        if half < 1e-30:
            continue
        rho = eta / half
        # identity: eta == rho * half  (trivially true; check no NaN/precision blowup)
        id_err = max(id_err, abs(eta - rho * half))
        etn = eta / sqn
        hfn = half / sqn
        if etn > best_eta[0]:
            best_eta = (etn, hfn)
        max_half = max(max_half, hfn)
        max_eta = max(max_eta, etn)
    mode = "FULL-Fp*" if full else "sampled"
    print(f"{n:>5} {p:>11} {id_err:>15.2e} {best_eta[0]:>13.4f} {best_eta[1]:>17.4f} "
          f"{max_half:>17.4f} {max_eta:>13.4f} {mode:>10}")

print()
print("READING:")
print("- identity_maxerr ~ 0 => |eta_b| = rho(b)*(|A|+|B|) holds (definitional sanity).")
print("- halfmass(b*)/sqn == |eta(b*)|/sqn  <=>  rho(b*)=1 (peak is the full half-mass, undamped).")
print("- max_halfmass/sqn vs max|eta|/sqn: if comparable + both grow like the period, the")
print("  factorization RELOCATES the wall onto the half-mass L1 (honest: NO escape, the half-mass")
print("  carries the same sqrt(n log) burden). A provably O(sqrt n) half-mass would be a lever (unlikely).")
