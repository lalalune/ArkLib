"""#407 NOT-RAMANUJAN lower bound on B = max_{b!=0}|eta_b|, eta_b = sum_{x in mu_n} e_p(bx).

Strengthens the char-0-energy lower bound  B^{2r} >= (q*E_r - n^{2r})/(q-1)  using the CLEAN,
PROVABLE char-0 energy lower bound (E_r(char-p) >= E_r(char-0) >= A_r):

    A_r := (2r-1)!! * (n/2)(n/2-1)...(n/2-r+1) * 2^r        [distinct-class antipodal pairs]

verified below to EQUAL the char-0 energy E_r whenever every antipodal class is used at most once
(it is the exact count of 2r-tuples that are a disjoint union of r antipodal pairs on DISTINCT
classes), so A_r <= E_r is an honest lower bound for ALL r (char-0, hence char-p).

Ceiling: A_r/n^r -> (2r-1)!! as n>>r^2, so  B >~ ((2r-1)!!)^{1/2r} * sqrt(n) ~ sqrt(2 r n / e).
NOT-RAMANUJAN (B > 2 sqrt n) requires ((2r-1)!!)^{1/2r} > 2, first true at r=6 (= 2.1614),
PROVIDED q clears the DC term n^{2r}: beta = log_n q > beta_thr(n), beta_thr -> 6 as n -> inf.

Run:  python3 scripts/probes/probe_407_notramanujan_threshold.py
"""
import numpy as np, sympy
from itertools import product
from collections import Counter
from math import log, sqrt, exp
import mpmath as mp
mp.mp.dps = 120


def doublefact(m):
    v = 1
    while m > 0:
        v *= m
        m -= 2
    return v


def er_char0(n, r):
    """Exact char-0 r-fold additive energy E_r of mu_n."""
    roots = [np.exp(2j * np.pi / n * k) for k in range(n)]
    if n ** r > 4_000_000:
        return None
    c = Counter()
    for tup in product(range(n), repeat=r):
        s = sum(roots[j] for j in tup)
        c[(round(s.real, 6), round(s.imag, 6))] += 1
    return sum(v * v for v in c.values())


def A_lb(n, r):
    """Distinct-class antipodal lower bound A_r = (2r-1)!! * (n/2)_r * 2^r  (<= E_r, all r)."""
    half = n // 2
    if r > half:
        return 0
    out = mp.mpf(doublefact(2 * r - 1)) * (mp.mpf(2) ** r)
    for t in range(r):
        out *= (half - t)
    return out


def realperiods(p, n):
    g = sympy.primitive_root(p)
    m = (p - 1) // n
    mu = [pow(g, (m * s) % (p - 1), p) for s in range(n)]
    return np.array([sum(np.exp(2j * np.pi * (b * x % p) / p) for x in mu).real
                     for b in range(1, p)])


print("=" * 92)
print("(0) A_r <= E_r honesty check (A_r = exact distinct-class antipodal count <= full energy):")
print(f"{'n':>3} {'r':>2} {'E_r(char0)':>11} {'A_r(LB)':>10} {'A_r<=E_r':>9}")
for n in [4, 6, 8]:
    for r in range(1, 4):
        if n ** (2 * r) > 4_000_000:
            continue
        E = er_char0(n, r)
        A = int(A_lb(n, r))
        print(f"{n:>3} {r:>2} {str(E):>11} {A:>10} {str(A <= E):>9}")

print("\n" + "=" * 92)
print("(1) Asymptotic ceiling constant ((2r-1)!!)^{1/2r} (crosses 2 at r=6):")
print(f"{'r':>3} {'((2r-1)!!)^(1/2r)':>18} {'>2?':>5}")
for r in range(1, 9):
    c = doublefact(2 * r - 1) ** (1 / (2 * r))
    print(f"{r:>3} {c:>18.4f} {str(c > 2):>5}")

print("\n" + "=" * 92)
print("(2) NOT-RAMANUJAN beta threshold (min over r of beta s.t. B>2sqrt n provable):")
print(f"{'n':>20} {'r*':>3} {'beta_thr':>9}")
for n in [2**8, 2**10, 2**12, 2**16, 2**20, 2**24, 2**30, 2**40, 2**60]:
    best = None
    br = None
    for r in range(6, 60):
        if r > n // 2:
            break
        Ar = A_lb(n, r)
        nr = mp.mpf(n) ** r
        four = mp.mpf(4) ** r
        denom = Ar - four * nr
        if denom <= 0:
            continue
        numer = mp.mpf(n) ** (2 * r) - four * nr
        Q = numer / denom
        beta = mp.log(Q) / mp.log(n)
        if best is None or beta < best:
            best = beta
            br = r
    print(f"{n:>20} {br:>3} {float(best):>9.4f}")

print("\n" + "=" * 92)
print("(3) Prize regime n=2^30, q~n*2^128~2^158, beta=5.27: best achievable r and B/sqrt(n):")
n = 2**30
q = n * (2**128)
beta = log(q) / log(n)
sq = sqrt(n)
best = mp.mpf(0)
bestr = 0
for r in range(1, 12):
    Ar = A_lb(n, r)
    num = mp.mpf(q) * Ar - mp.mpf(n) ** (2 * r)
    if num <= 0:
        continue
    lb = (num / mp.mpf(q - 1)) ** (mp.mpf(1) / (2 * r))
    if lb > best:
        best = lb
        bestr = r
print(f"  beta={beta:.4f}; best r*={bestr}, B>= {float(best):.2f} = {float(best)/sq:.4f} sqrt(n)"
      f"  (2 sqrt n = {2*sq:.0f})")
print(f"  => prize beta {beta:.2f} < threshold 5.58 (n=2^30): method gives 1.984 sqrt n, NOT > 2 sqrt n.")
print(f"     NOT-RAMANUJAN is a clean theorem only for beta above the threshold (honest scope).")

print("\n" + "=" * 92)
print("(4) Real-period verification of the average lower bound (small n, achievable r<=n/2):")
print(f"{'p':>10} {'n':>3} {'beta':>5} {'B(true)':>9} {'LB(A_r)':>9} {'2sqrtn':>8} {'r*':>3}")
for (p, n) in [(769, 8), (12289, 8), (786433, 8), (769, 16), (12289, 16), (786433, 16)]:
    if (p - 1) % n or not sympy.isprime(p):
        continue
    eta = realperiods(p, n)
    B = eta.max()
    beta = log(p) / log(n)
    best = 0.0
    bestr = 0
    for r in range(1, 9):
        if r > n // 2:
            break
        Ar = float(A_lb(n, r))
        num = p * Ar - n ** (2 * r)
        if num <= 0:
            continue
        lb = (num / (p - 1)) ** (1 / (2 * r))
        if lb > best:
            best = lb
            bestr = r
    ok = "OK" if best <= B + 1e-6 else "VIOLATION"
    print(f"{p:>10} {n:>3} {beta:>5.2f} {B:>9.3f} {best:>9.3f} {2*sqrt(n):>8.3f} {bestr:>3}  [{ok}]")
