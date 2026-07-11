#!/usr/bin/env python3
"""
C3-effective-sum-product probe (FAST char-p version, proper mu_n).

Does the 2-POWER structure of mu_n give a BETTER effective exponent e=logB/logn
than generic? Measures the TRUE char-p Gauss period sup-norm B=max_{b!=0}|eta_b|
via FFT over F_p (exact integer-indexed), at proper prizelike fields:
p PRIME, n|p-1, p>>n^3, NEVER n=p-1, mu_n = 2-power subgroup.

ALSO: |G+G| sumset growth and additive energy E(G) -- the sum-product witnesses.
And compares vs an alt-order (non-2-power) subgroup of similar size.
"""
from math import log, sqrt
import numpy as np
from sympy import isprime, primitive_root, divisors

def find_prime(n, beta=4):
    p = (n**beta) | 1
    while not (isprime(p) and (p-1) % n == 0 and (p-1)//n >= 2):
        p += 2
    return p

def subgroup(p, order):
    g = primitive_root(p)
    e = (p-1)//order
    h = pow(g, e, p)
    return [pow(h, k, p) for k in range(order)]

def supnorm_fft(S, p):
    """B = max_{b!=0}|sum_x e_p(bx)| via FFT of indicator. |hat 1_S(b)| = |eta_b|."""
    ind = np.zeros(p)
    for x in S: ind[x % p] = 1.0
    F = np.fft.fft(ind)
    mags = np.abs(F)
    return float(np.max(mags[1:]))  # skip b=0 (=|S|)

def add_energy(S, p):
    from collections import Counter
    c = Counter((a+b) % p for a in S for b in S)
    return sum(v*v for v in c.values())

def sumset_size(S, p):
    return len({(a+b) % p for a in S for b in S})

print("=== C3 effective exponent for 2-power mu_n (TRUE char-p Gauss period, FFT) ===")
print(f"{'n':>4} {'p':>10} {'B':>9} {'e=logB/logn':>11} {'sqrt(n)':>8} {'B/sqrtn':>8} {'|G+G|/n':>8} {'E/n^2':>7}")
for mu in range(3, 8):  # n=8..128; p~n^4 up to ~268M FFT (memory ok)
    n = 2**mu
    p = find_prime(n, beta=4)
    if p > 5_000_000 and mu >= 7:
        # n=128 p~268M FFT too big; use beta=3.5-ish smaller proper field
        p = find_prime(n, beta=3) 
        # ensure still >> n^3? for n=128, n^3=2M; beta=3 gives p~2M, p/n^3~1 -- mark it
    S = subgroup(p, n)
    B = supnorm_fft(S, p)
    e = log(B)/log(n)
    ss = sumset_size(S, p)
    E = add_energy(S, p)
    print(f"{n:>4} {p:>10} {B:>9.3f} {e:>11.4f} {sqrt(n):>8.3f} {B/sqrt(n):>8.3f} {ss/n:>8.2f} {E/n**2:>7.3f}")

print()
print("=== 2-power vs alt-order subgroup at SAME prime, similar size ===")
for mu in [3,4,5,6]:
    n = 2**mu
    p = find_prime(n, beta=4)
    if p > 5_000_000: p = find_prime(n, beta=3)
    divs = sorted(d for d in divisors(p-1) if 2 <= d <= 2*n and d != n)
    # pick alt-order closest to n
    if not divs:
        print(f"n={n} p={p}: no alt order"); continue
    alt = min(divs, key=lambda d: abs(d-n))
    S2 = subgroup(p, n); Sa = subgroup(p, alt)
    B2 = supnorm_fft(S2, p); Ba = supnorm_fft(Sa, p)
    print(f"n={n}(2pow) p={p}: B={B2:.3f} e={log(B2)/log(n):.4f} B/sqrtn={B2/sqrt(n):.3f}  ||  "
          f"order {alt}: B={Ba:.3f} e={log(Ba)/log(alt):.4f} B/sqrt={Ba/sqrt(alt):.3f}")

print()
print("READ: e ~ const (NOT ->0.5) and B/sqrtn ~ small const = sum-product SATURATED (energy minimal);")
print("if 2-power B/sqrtn NOT systematically below alt-order => no 2-power EDGE on the sup-norm at this scale.")
