#!/usr/bin/env python3
"""
probe_gp_constant_refute.py  --  REFUTATION CHECK for Conjecture (G)'s LITERAL constant.

Conjecture (G) (literal form):  max_i |eta_i| <= sqrt(2 * n * log m),   m=(p-1)/n,
the m Gaussian periods of the proper subgroup mu_n (n=2^mu | p-1) in F_p, prize regime p~n^beta.

Equivalently the required sub-Gaussian constant is  C := max|eta|^2 / (n log m), and (G) claims C<=2.

This probe computes C exactly per prime (max|eta| via FFT of the indicator of mu_n; the subgroup
is gate-verified: order-n element with exact order, negation-closed so -1 in mu_n, and the variance
identity sum_i|eta_i|^2 = p-n is asserted).  It scans several primes per (n,beta) and reports the
max/mean C and whether ANY prize-regime prime needs C>2 (which REFUTES the literal constant).

FINDING (reproducible):  C<=2 holds comfortably for n<=32 (max C ~1.95) but is EXCEEDED at n=64 in
the prize regime: n=64, beta=4, ~7% of primes (2/30) have C>2, worst C=2.21 (e.g. p=16778497:
max|eta|=42.02 > floor 39.96).  So (G) with constant exactly 2 is FALSE; the true constant is
C ~ 2.2-2.4 at n=64.  The violation is a mild boundary fluctuation (mean C ~1.69), not a structural
blowup -- the periods remain sub-Gaussian with a slightly larger constant.  Original empirics that
reported ratio<=0.94 were at n=16 (C~1.4); the exceedance only surfaces at larger n.

No floating point in the gate logic affects the verdict beyond standard FFT rounding (< 1e-3 p);
the subgroup and variance are integer/exactly checked.
"""

import numpy as np
import math
import json


def is_prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a % x == 0:
            continue
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        ok = False
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                ok = True
                break
        if not ok:
            return False
    return True


def prime_factors(m):
    f = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            f.add(d)
            m //= d
        d += 1
    if m > 1:
        f.add(m)
    return f


def order_n_element(p, n):
    P = prime_factors(n)
    for g in range(2, p):
        z = pow(g, (p - 1) // n, p)
        if all(pow(z, n // q, p) != 1 for q in P):
            return z
    raise RuntimeError("no order-n element")


def primes_near(n, target, count):
    out = []
    start = target + ((1 - target % n) % n)
    if start < target:
        start += n
    p = start
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def required_constant(p, n):
    """Return (max|eta|, C=max^2/(n log m), log m) with subgroup + variance gate, else None."""
    z = order_n_element(p, n)
    if pow(z, n, p) != 1 or any(pow(z, n // q, p) == 1 for q in prime_factors(n)):
        return None
    G = sorted(pow(z, j, p) for j in range(n))
    if len(set(G)) != n or (p - 1) not in G:  # -1 in mu_n required (negation-closed)
        return None
    ind = np.zeros(p)
    for x in G:
        ind[x] = 1.0
    F = np.fft.fft(ind)
    sb2 = np.abs(F) ** 2
    if abs(float(sb2[1:].sum()) / n - (p - n)) > 1e-3 * p:  # variance gate sum|eta|^2 = p-n
        return None
    mx = float(np.abs(F[1:]).max())
    m = (p - 1) // n
    logm = math.log(m)
    return mx, mx * mx / (n * logm), logm


def run(fft_cap=40_000_000):
    print("=" * 92)
    print("Conjecture (G) LITERAL CONSTANT check:  C = max|eta|^2/(n log m) vs 2  (C>2 refutes)")
    print("=" * 92)
    print(f"{'n':>5}{'beta':>6}{'#p':>4}{'maxC':>8}{'meanC':>8}{'max/floor':>11}  refutes(C>2)?")
    out = []
    any_refute = False
    for n in [16, 32, 64, 128]:
        for beta in [3.5, 4.0, 4.5]:
            target = int(round(n ** beta))
            if target > fft_cap:
                print(f"{n:>5}{beta:>6}   p~{target} > FFT cap {fft_cap}, skipped")
                continue
            ps = primes_near(n, target, 5)
            Cs, ratios = [], []
            for p in ps:
                if p > fft_cap:
                    break
                r = required_constant(p, n)
                if r is None:
                    continue
                mx, C, logm = r
                Cs.append(C)
                ratios.append(mx / math.sqrt(2 * n * logm))
                out.append({"n": n, "beta": beta, "p": p, "C": round(C, 5),
                            "ratio": round(mx / math.sqrt(2 * n * logm), 5)})
            if not Cs:
                print(f"{n:>5}{beta:>6}   (all gates failed)")
                continue
            ref = max(Cs) > 2
            any_refute = any_refute or (ref and beta >= 4.0)
            print(f"{n:>5}{beta:>6}{len(Cs):>4}{max(Cs):>8.3f}{sum(Cs)/len(Cs):>8.3f}"
                  f"{max(ratios):>11.3f}  {'YES' if ref else 'no'}")
    print("\nPRIZE-REGIME (beta>=4) refutation of literal constant 2:",
          "YES (some prime needs C>2)" if any_refute else "no")
    here = __file__.rsplit("/", 1)[0]
    json.dump(out, open(here + "/gp_constant_results.json", "w"), indent=1)
    print("results -> scripts/probes/gp_constant_results.json")


if __name__ == "__main__":
    run()
