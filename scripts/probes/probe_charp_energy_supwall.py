#!/usr/bin/env python3
"""
probe_charp_energy_supwall.py

Directly test the char-p transfer linchpin behind the prize wall:
  Is  E_r(F_p)  (additive energy of the n-th roots of unity, mult. subgroup of
  order n in F_p^*)  bounded by the Gaussian/Wick bound  (2r-1)!! * n^r  for all
  primes p in the prize-relevant range, or does sup_p E_r(F_p) outgrow it (the
  spurious-collision excess W_r = E_r(F_p) - E_r(C))?

We compute E_r(F_p) EXACTLY (integer) via r-fold cyclic convolution of the
indicator of R over Z/p, then E_r = sum_v c_r(v)^2, where
  c_r(v) = #{(x_1..x_r) in R^r : x_1+...+x_r = v (mod p)}.

We use integer convolution (numpy int64 via direct polynomial mult mod p index),
which is exact for these sizes. We sweep all p = 1 mod n up to P_MAX, track
  max_p E_r(F_p),  the Gaussian bound G_r = (2r-1)!! * n^r,
  the excess ratio max_p E_r / G_r,  and which p achieves the max.

If the ratio stays <= 1 the Wick bound holds on the sampled range; if it grows
with r that quantifies the wall.
"""
import numpy as np
from sympy import isprime, primitive_root

def double_factorial_odd(twoR_minus_1):
    # (2r-1)!! = product of odd numbers up to 2r-1
    p = 1
    k = twoR_minus_1
    while k > 0:
        p *= k
        k -= 2
    return p

def roots_of_unity_subgroup(p, n):
    """Return the n elements of the order-n multiplicative subgroup of F_p^*."""
    g0 = primitive_root(p)
    g = pow(g0, (p - 1) // n, p)  # primitive n-th root of unity
    R = []
    cur = 1
    for _ in range(n):
        R.append(cur)
        cur = (cur * g) % p
    return R

def energy_Er(p, R, r):
    """Exact E_r(F_p) = sum_v c_r(v)^2 via r-fold cyclic convolution over Z/p.

    c_1 = indicator of R; c_{k+1}[v] = sum_{x in R} c_k[(v-x) mod p].
    Each step is n cyclic shifts of an int64 vector => O(n*p), exact.
    """
    c = np.zeros(p, dtype=np.int64)
    for x in R:
        c[x] += 1
    Rs = list(R)
    for _ in range(r - 1):
        new = np.zeros(p, dtype=np.int64)
        for x in Rs:
            new += np.roll(c, x)   # shift by x mod p (np.roll wraps => cyclic)
        c = new
    # E_r = sum c^2 ; use python-int sum to avoid any int64 overflow on the square-sum
    cc = c.astype(object)
    return int(np.sum(cc * cc))

def main():
    print("=== char-p additive-energy sup-wall probe ===")
    print("E_r(F_p) for R = order-n subgroup; compare to Gaussian bound G_r=(2r-1)!!*n^r\n")
    for n in [8, 16]:
        print(f"--- n = {n} ---")
        for r in range(2, 7):
            Gr = double_factorial_odd(2 * r - 1) * (n ** r)
            best = -1
            best_p = None
            count_primes = 0
            # sweep primes p = 1 mod n; cap work
            P_MAX = 40000 if n == 8 else 50000
            p = n + 1
            while p <= P_MAX:
                if isprime(p) and (p - 1) % n == 0:
                    R = roots_of_unity_subgroup(p, n)
                    Er = energy_Er(p, R, r)
                    count_primes += 1
                    if Er > best:
                        best = Er
                        best_p = p
                p += 1
            ratio = best / Gr if Gr else float('nan')
            flag = "  <-- EXCEEDS Gaussian" if ratio > 1.0 else ""
            print(f"  r={r}: G_r=(2r-1)!!*n^r={Gr:>14}  max_p E_r={best:>14} (p={best_p})  "
                  f"ratio={ratio:6.3f}  [{count_primes} primes]{flag}")
        print()

if __name__ == "__main__":
    main()
