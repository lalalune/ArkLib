#!/usr/bin/env python3
"""
probe_charp_energy_thin.py

Corrected prize-regime test of the char-p transfer linchpin.

The previous probe (probe_charp_energy_supwall.py) was maximized at p=17 where
n=p-1, i.e. R = ALL of F_p^* (DENSE, n~p) — the opposite of the prize regime.
There the Gaussian bound (2r-1)!!*n^r fails by up to ~95x, but that case is
off-regime and irrelevant.

The PRIZE REGIME is THIN: q ~ n^4..n^5, i.e. n ~ q^{1/4..1/5}, so the order-n
subgroup R is a sparse multiplicative subgroup. Here we restrict to primes
  p in [n^4, n^5]   (so n <= p^{1/4}, genuinely thin)
and measure sup_p E_r(F_p) / [(2r-1)!!*n^r].

If sup stays ~1 the Gaussian bound holds on-regime; if it grows with r/p the
wall (excess W_r) is real even in the thin regime.

Exact integer energy via O(n*p) cyclic-shift convolution.
"""
import numpy as np
from sympy import isprime, primitive_root, nextprime

def double_factorial_odd(m):
    p, k = 1, m
    while k > 0:
        p *= k; k -= 2
    return p

def subgroup(p, n):
    g0 = primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    R, cur = [], 1
    for _ in range(n):
        R.append(cur); cur = (cur * g) % p
    return R

def energy_Er(p, R, r):
    c = np.zeros(p, dtype=np.int64)
    for x in R:
        c[x] += 1
    for _ in range(r - 1):
        new = np.zeros(p, dtype=np.int64)
        for x in R:
            new += np.roll(c, x)
        c = new
    cc = c.astype(object)
    return int(np.sum(cc * cc))

def sample_thin_primes(n, n_samples):
    """primes p ≡ 1 (mod n) in [n^4, n^5], sampled across the range."""
    lo, hi = n**4, n**5
    # cap hi for compute feasibility
    hi = min(hi, lo * 24)
    out, seen = [], set()
    step = max(1, (hi - lo) // (n_samples * 2))
    x = lo
    while x <= hi and len(out) < n_samples:
        # next prime ≡ 1 mod n at/after x
        cand = x - (x % n) + 1
        if cand < x:
            cand += n
        while cand <= hi:
            if isprime(cand) and cand not in seen:
                out.append(cand); seen.add(cand); break
            cand += n
        x += step
    return out, lo, hi

def main():
    print("=== THIN-regime char-p energy probe (prize regime p in [n^4, n^5]) ===")
    print("E_r(F_p), R = order-n subgroup; vs Gaussian G_r=(2r-1)!!*n^r\n")
    for n in [8, 16]:
        primes, lo, hi = sample_thin_primes(n, 60 if n == 8 else 24)
        print(f"--- n={n}  thin window p in [{lo}, {hi}]  ({len(primes)} primes sampled, "
              f"p^(1/4) in [{lo**0.25:.1f},{hi**0.25:.1f}]) ---")
        for r in range(2, 7):
            Gr = double_factorial_odd(2 * r - 1) * (n ** r)
            best, best_p, tot, cnt = -1, None, 0.0, 0
            for p in primes:
                R = subgroup(p, n)
                Er = energy_Er(p, R, r)
                tot += Er / Gr; cnt += 1
                if Er > best:
                    best, best_p = Er, p
            ratio = best / Gr
            avg = tot / cnt if cnt else float('nan')
            flag = "  <-- EXCEEDS" if ratio > 1.0 else "  (within)"
            print(f"  r={r}: G_r={Gr:>15}  sup E_r/G_r={ratio:7.4f} (p={best_p})  "
                  f"mean E_r/G_r={avg:7.4f}{flag}")
        print()

if __name__ == "__main__":
    main()
