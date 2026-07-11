#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — coherent-set probe v2: ADVERSARIAL re-check of the ~50% near-coherent finding.

v1 found: ~50% of b have index-2 coset-half coherence rho(b) >= 0.99, FLAT across n=16..128.
That ~0.50 is suspiciously clean -> could be an index-2 SIGN/PARITY artifact (the two halves A,B
being trivially real-aligned for half of b). Before any DEAD verdict, re-check adversarially:

(C1) Is the ~50% a real-piece SIGN artifact? rho=1 <=> A,B same-ray. For the index-2 split, when
     is A+B trivially aligned? Decompose: report the fraction where A,B are (near) same-ray AND
     whether that coincides with a simple congruence on b (sign artifact) vs genuinely spread.
(C2) THE PRIZE OBJECT is NOT the index-2 split coherence per se — it's whether |eta_b| itself is
     large. Cross-check: does high rho(b) correlate with LARGE |eta_b| (the actual prize size)?
     If the near-coherent b have SMALL |eta_b| (coherence of two small pieces is meaningless), the
     ~50% is irrelevant to the prize. Report joint (rho, |eta_b|/sqrt(n)).
(C3) The worst-b for the PRIZE = argmax |eta_b|. Report rho at the true argmax (full or large
     sample) and the |eta_b|/sqrt(n) there. Is the prize-worst-b in the near-coherent set?

EXACT complex arithmetic, PROPER mu_n, p>>n^3, NEVER n=q-1.
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


def analyze(n, p, g, sample):
    m = (p - 1) // n
    h = pow(g, m, p)
    mu = [pow(h, j, p) for j in range(n)]
    even = [mu[j] for j in range(0, n, 2)]
    odd = [mu[j] for j in range(1, n, 2)]
    ep = lambda t: cmath.exp(2j * math.pi * (t % p) / p)
    sqn = math.sqrt(n)
    best = (-1.0, None, None)   # (|eta|/sqrt n, rho, b)
    near_coh_small = 0          # near-coherent AND small |eta|
    near_coh_total = 0
    samp_rhoeta = []
    for b in sample:
        A = sum(ep(b * y) for y in even)
        B = sum(ep(b * y) for y in odd)
        denom = abs(A) + abs(B)
        if denom < 1e-12:
            continue
        rho = abs(A + B) / denom
        eta = abs(A + B)
        etn = eta / sqn
        samp_rhoeta.append((rho, etn))
        if etn > best[0]:
            best = (etn, rho, b)
        if rho >= 0.99:
            near_coh_total += 1
            if etn < 1.0:           # |eta| < sqrt(n): coherence of two SMALL pieces
                near_coh_small += 1
    # correlation of rho with normalized |eta|
    import statistics
    rs = [x[0] for x in samp_rhoeta]
    es = [x[1] for x in samp_rhoeta]
    try:
        corr = statistics.correlation(rs, es)
    except Exception:
        corr = float('nan')
    # mean |eta|/sqrt n among near-coherent vs all
    eta_nc = [e for (r, e) in samp_rhoeta if r >= 0.99]
    mean_eta_nc = sum(eta_nc) / len(eta_nc) if eta_nc else float('nan')
    mean_eta_all = sum(es) / len(es) if es else float('nan')
    frac_small = (near_coh_small / near_coh_total) if near_coh_total else float('nan')
    return best, corr, mean_eta_nc, mean_eta_all, frac_small


print("ADVERSARIAL re-check of ~50% near-coherent finding")
print(f"{'n':>5} {'p':>12} {'argmax|eta|/sqn':>15} {'rho@worst':>10} {'corr(rho,eta)':>13} "
      f"{'meanEta_nc':>11} {'meanEta_all':>12} {'fracNCsmall':>12}")
for a in (4, 5, 6, 7):
    n = 2 ** a
    p = find_prime(n, 4.0)
    if p is None:
        continue
    g = primitive_root(p)
    cap = 8000
    random.seed(777 + n)
    sample = list(range(1, p)) if p - 1 <= cap else random.sample(range(1, p), cap)
    best, corr, mnc, mall, fsmall = analyze(n, p, g, sample)
    print(f"{n:>5} {p:>12} {best[0]:>15.4f} {best[1]:>10.4f} {corr:>13.4f} "
          f"{mnc:>11.4f} {mall:>12.4f} {fsmall:>12.4f}")

print()
print("KEY CHECKS:")
print("- fracNCsmall ~ 1 => most near-coherent b have |eta|<sqrt(n) (TINY) => the ~50% coherence")
print("  is coherence of NEGLIGIBLE pieces, IRRELEVANT to the prize (which is about LARGE |eta|).")
print("- corr(rho,eta) sign + rho@worst: is the PRIZE-worst-b (argmax|eta|) near-coherent?")
print("- meanEta_nc vs meanEta_all: do near-coherent b carry MORE or LESS mass than typical?")
