"""
wf407 / T389-01-deepmom : what the char-p energy actually IS at the saddle depth,
and why the moment method cannot use it.

Established (threshold.py):
  - char-0 bound E_r^(0) <= (2r-1)!! n^r : THEOREM (Bessel), never fails.
  - char-p E_r^(p) >= E_r^(0), with EQUALITY iff p > tau_r ~ n^{(r+3)/2}, i.e. r <= r_max = 2 log_n p - 3.

This probe quantifies, at a FIXED prize-like prime, how the char-p moment ladder
E_r^(p) behaves as r crosses r_max, and confirms the moment bound (p E_r^(p))^{1/2r}
on B = max|eta_b|:
  - for r <= r_max it tracks the clean Gaussian (p E_r^(0))^{1/2r}
  - for r >= r_max it BLOWS UP because E_r^(p) saturates toward the trivial n^{2r} (all
    subsets collide mod p), so the (p E_r)^{1/2r} bound stops improving and the optimum
    is pinned at r_max, giving B <~ n^{3/4} sqrt(log_n p), NOT sqrt(n log p).
We verify (p E_r^(p))^{1/2r} achieves its MIN exactly near r_max and equals the true
B = max_{b!=0}|eta_b| only up to the moment slack.
"""

import itertools
import math
from math import log, sqrt
from collections import Counter
from sympy import primerange


def is_prim_root(g, p):
    cur = g % p
    order = 1
    while cur != 1:
        cur = (cur * g) % p
        order += 1
        if order > p:
            return False
    return order == p - 1


def mu_n_charp(n, p):
    for cand in range(2, p):
        if is_prim_root(cand, p):
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]


def energy_charp(n, r, p, roots):
    sums = Counter()
    for tup in itertools.product(roots, repeat=r):
        sums[sum(tup) % p] += 1
    return sum(c * c for c in sums.values())


def true_B(n, p, roots):
    """max_{b!=0} |sum_{x in mu_n} e_p(b x)| exactly."""
    best = 0.0
    for b in range(1, p):
        re = im = 0.0
        for x in roots:
            ang = 2 * math.pi * (b * x % p) / p
            re += math.cos(ang)
            im += math.sin(ang)
        v = math.hypot(re, im)
        if v > best:
            best = v
    return best


def doublefact_odd(r):
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


print("=" * 84)
print("SADDLE BEHAVIOUR: the moment bound (p*E_r^(p))^{1/2r} vs r, across r_max.")
print("=" * 84)

# pick n and a prize-like-ish prime (small enough to enumerate true B and E_r up to r~5)
# we want p ~ n^beta with beta moderate so r_max = 2 log_n p - 3 is a few.
cases = [
    (8, None),   # choose largest enumerable prime ≡1 mod 8 with p ~ n^3..4
    (16, None),
]
# choose primes
chosen = []
for n in (8, 16):
    plist = [p for p in primerange(2, 80000) if p % n == 1]
    # pick a prime near n^3.5 (so r_max ~ 4) that's enumerable
    target = n ** 3.5
    p = min(plist, key=lambda x: abs(x - target))
    chosen.append((n, p))

for n, p in chosen:
    roots = mu_n_charp(n, p)
    beta = log(p, n)
    r_max = 2 * beta - 3
    B = true_B(n, p, roots)
    print(f"\n### n={n}, p={p}  (beta=log_n p={beta:.2f}, r_max=2 log_n p -3={r_max:.2f}) ###")
    print(f"    true B = max_b!=0 |eta_b| = {B:.4f}   (sqrt(n)={sqrt(n):.4f}, "
          f"sqrt(n*ln p)={sqrt(n*math.log(p)):.4f}, n^0.75={n**0.75:.4f})")
    print(f"    {'r':>2} {'E_r^(0)':>10} {'E_r^(p)':>12} {'defect%':>8} "
          f"{'(p E_r^p)^{1/2r}':>16} {'(p E_r^0)^{1/2r}':>16}  beats B?")
    rmax_enum = 5 if n == 8 else 4
    e0_cache = {}
    # char0 energy
    def root_vec(k):
        half = n // 2
        v = [0]*half
        sign = 1 if (k//half)%2==0 else -1
        v[k%half]+=sign
        return v
    rc=[root_vec(k) for k in range(n)]
    def e0(r):
        half=n//2
        sums=Counter()
        for tup in itertools.product(range(n),repeat=r):
            v=[0]*half
            for k in tup:
                t=rc[k]
                for j in range(half): v[j]+=t[j]
            sums[tuple(v)]+=1
        return sum(c*c for c in sums.values())
    for r in range(2, rmax_enum + 1):
        if n ** r > 6_000_000:
            break
        E0 = e0(r)
        Ep = energy_charp(n, r, p, roots)
        defect = 100.0 * (Ep - E0) / E0
        mom_p = (p * Ep) ** (1.0 / (2 * r))
        mom_0 = (p * E0) ** (1.0 / (2 * r))
        beats = "yes" if mom_p <= B * 1.0001 else "no"
        print(f"    {r:>2} {E0:>10} {Ep:>12} {defect:>7.1f}% {mom_p:>16.4f} "
              f"{mom_0:>16.4f}   {beats}")

print()
print("=" * 84)
print("CONCLUSION CHECK")
print("=" * 84)
print("If the (p E_r^p)^{1/2r} column reaches its MIN near r=r_max and then GROWS as the")
print("defect% explodes (E_r^p -> n^{2r}), that confirms: the moment method's optimum is")
print("PINNED at r_max by the char-p transfer failure, NOT by the char-0 bound (which is")
print("a theorem). The wall is the char-p transfer at r>=r_max.")
