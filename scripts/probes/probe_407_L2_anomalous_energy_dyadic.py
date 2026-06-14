#!/usr/bin/env python3
"""#407 LANE L2 — constant-index large-subgroup ANOMALOUS additive energy A_k.

PRIZE REGIME (this is the point the prior structural probe missed): the prize forces
index m = (p-1)/n CONSTANT but LARGE (~2^128), n = 2^mu -> infty.  Earlier probes swept
small even n with TINY index m<=16 (subgroup nearly fills the field, K=|mu_n+mu_n|/n ~ m
~ O(1)).  Here mu_n is GENUINELY SPARSE (n^2 << p), the regime that controls the prize.

OBJECT (the only un-refuted closure path):
    E_k(mu_n) := #{ (x_1..x_k, y_1..y_k) in mu_n^{2k} : sum x_i = sum y_j  (mod p) }
               = sum_s r_k(s)^2,   r_k(s) = #{k-tuples from mu_n summing to s}.
    A_k := E_k - n^{2k}/p     (the ANOMALOUS energy = char-p deviation from random main).

The b!=0 moment identity  sum_{b!=0} ||eta_b||^{2k} = q * A_k  (the b=0 term n^{2k} is the
n^{2k}/p * p removed).  Moment closure of the prize needs
    A_k  <=  C^k * k! * n^k     for all k up to ~ ln p,
then optimizing k ~ ln p gives  max_b||eta_b|| <= sqrt(2 n ln p) << n  = CLOSURE.

CHAR-0 BENCHMARK (Lam-Leung / DyadicEnergyK1.lean): over C, E_k(mu_n) <= (2k-1)!! n^k, with
EXACT  E_2 = 3n^2-3n,  E_3 = 15n^3-45n^2+40n  (negation-closed dyadic).  Note (2k-1)!! = k! * 2^k/...
actually (2k-1)!! ~ sqrt(2)(2k/e)^k, and k! 2^k ~ (2k/e)^k sqrt(2 pi k) -- comparable; both give
A_k <~ k! n^k up to a base-C factor.  The target C^k k! n^k is the SAME SHAPE as char-0.

THE QUESTION (decisive, dyadic, large n, fixed large index):
  Is  A_k / (k! n^k)  BOUNDED, GROWING, or DECAYING in n at FIXED large index m?
   * BOUNDED/decaying  ==> the constant-index regime is OFF the BGK wall; closure shape holds.
   * GROWING in n      ==> A_k inherits the wall; no constant-rate closure.

Everything is EXACT (integer cyclotomic-domain build + FFT cyclic convolution with round-trip
integrality check; never sampled).  We sweep dyadic n=2^mu and large m = 2^a.
"""

import sys
from math import comb, log
from collections import Counter
import numpy as np


def isprime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    if x % 3 == 0:
        return x == 3
    d = 5
    while d * d <= x:
        if x % d == 0 or x % (d + 2) == 0:
            return False
        d += 6
    return True


def primroot(p):
    if p == 2:
        return 1
    fac = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for a in range(2, p):
        if all(pow(a, (p - 1) // q, p) != 1 for q in fac):
            return a
    return None


def domain(p, n):
    """The n-th roots of unity mu_n in F_p (n | p-1), as a list of residues."""
    g = pow(primroot(p), (p - 1) // n, p)
    dom = [pow(g, i, p) for i in range(n)]
    assert len(set(dom)) == n, "subgroup degenerate"
    return dom


def find_const_index_prime(mu, a):
    """For n = 2^mu, find smallest prime p = m*n + 1 with m = 2^a * t, t odd >= 1,
    so the index m >= 2^a is as close to 2^a as possible (constant LARGE index)."""
    n = 1 << mu
    base = 1 << a
    # we want p = m*n+1 prime with m >= base, smallest such; report actual m.
    m = base
    while True:
        p = m * n + 1
        if isprime(p):
            return p, n, m
        m += 1


def rk_counts(p, dom, k):
    """r_k(s) length-p exact int array via k-fold cyclic convolution (FFT round-trip checked)."""
    r1 = np.zeros(p)
    for x in dom:
        r1[x] += 1.0
    F = np.fft.rfft(r1)
    rk_f = np.fft.irfft(F ** k, n=p)
    rk = np.rint(rk_f)
    if float(np.max(np.abs(rk_f - rk))) > 0.4:
        return None  # FFT precision insufficient
    rki = rk.astype(np.int64)
    if int(rki.sum()) != len(dom) ** k:
        return None
    return rki


def Ek(p, dom, k):
    rk = rk_counts(p, dom, k)
    if rk is None:
        return None
    # sum of squares as python int (avoid int64 overflow for large)
    return sum(int(v) * int(v) for v in rk.tolist())


def kfact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def dfact_odd(k):
    r = 1
    for j in range(1, k + 1):
        r *= (2 * j - 1)
    return r


print("=" * 100, flush=True)
print("L2 ANOMALOUS ENERGY  A_k = E_k(mu_n) - n^{2k}/p   for DYADIC n=2^mu, CONSTANT LARGE index m", flush=True)
print("target (closure):  A_k <= C^k k! n^k   <=>   A_k/(k! n^k) bounded/decaying in n at fixed m", flush=True)
print("=" * 100, flush=True)

# ---------------------------------------------------------------------------
# Main sweep: fixed large index 2^a, dyadic n=2^mu growing, k=2,3,4.
# FFT array length p = m*n+1 ~ 2^(a+mu); feasible up to ~ a few *10^7 entries.
# ---------------------------------------------------------------------------
for a in [7, 8, 9, 10, 11, 12]:
    print(f"\n### index m ~ 2^{a} = {1<<a}   (n^2/p ~ n/m = sparse iff n << m: prize-faithful)", flush=True)
    print(f"{'mu':>3} {'n':>7} {'m':>7} {'p':>10} {'n^2/p':>8} "
          f"{'A2/(2!n^2)':>11} {'A3/(3!n^3)':>11} {'A4/(4!n^4)':>11} "
          f"{'A2/c0_2':>8} {'A3/c0_3':>8}", flush=True)
    for mu in range(3, 17):
        n = 1 << mu
        try:
            p, n, m = find_const_index_prime(mu, a)
        except Exception:
            continue
        if p > 60_000_000:   # FFT length guard (~60M doubles = 480MB for rfft)
            break
        dom = domain(p, n)
        e2 = Ek(p, dom, 2)
        e3 = Ek(p, dom, 3)
        e4 = Ek(p, dom, 4) if p <= 30_000_000 else None
        if e2 is None or e3 is None:
            print(f"{mu:>3} {n:>7} {m:>7} {p:>10}  FFT-precision-fail", flush=True)
            continue
        A2 = e2 - n ** 4 / p
        A3 = e3 - n ** 6 / p
        r2 = A2 / (kfact(2) * n ** 2)
        r3 = A3 / (kfact(3) * n ** 3)
        if e4 is not None:
            A4 = e4 - n ** 8 / p
            r4 = A4 / (kfact(4) * n ** 4)
            r4s = f"{r4:>11.4f}"
        else:
            r4s = f"{'--':>11}"
        c0_2 = 3 * n ** 2 - 3 * n           # char-0 E_2 (=A_2 char-0, main->0)
        c0_3 = 15 * n ** 3 - 45 * n ** 2 + 40 * n
        print(f"{mu:>3} {n:>7} {m:>7} {p:>10} {n*n/p:>8.4f} "
              f"{r2:>11.4f} {r3:>11.4f} {r4s} "
              f"{A2/c0_2:>8.4f} {A3/c0_3:>8.4f}", flush=True)

print("\n" + "=" * 100, flush=True)
print("READ: at FIXED index column, scan A_k/(k! n^k) DOWN the n (mu) rows.", flush=True)
print(" * ratio flat/decaying as n grows  => A_k <= C^k k! n^k holds; constant-index regime OFF the wall.", flush=True)
print(" * ratio GROWING with n            => A_k inherits BGK; no constant-rate moment closure.", flush=True)
print(" * A_k/c0_k near 1 and stable      => char-p A_k tracks the char-0 Lam-Leung shape (E_k=(2k-1)!!n^k).", flush=True)
print("=" * 100, flush=True)
