#!/usr/bin/env python3
"""#444 — EXACT (no-float) independent cross-check of `probe_onset_growth_law.py`.

`probe_onset_growth_law.py` measures the wraparound onset law
    r_0(n,p) = first r with E_r(F_p) != E_r(C)  ~  p^{1/phi(n)}
(the law cited by `Frontier/_OnsetGrowthLaw.lean`, which shows the onset is BELOW the saddle
r* ~ log p at prize scale). That probe computes the char-0 baseline E_r(C) by FLOAT rounding
`round(sum(cmath.exp(...)).real, 5)` — the single fragile step (collision grouping by rounded
floats can in principle mis-merge / split classes).

This probe removes that fragility: it computes E_r(C) EXACTLY by counting in the cyclotomic
ring Z[zeta_n] coordinate basis. For n a power of 2, zeta^(n/2) = -1, so a length-r sum of
n-th roots with class-counts (k_0,...,k_{n-1}) lands at the exact integer coordinate vector
    (k_j - k_{j+n/2})_{j<n/2}   in   Z[zeta_n] = Z^{phi(n)},
and E_r(C) = sum over coordinate classes of (multinomial weight)^2. No float anywhere.
E_r(F_p) is the exact integer mod-p collision count (independently re-derived here).

Stdlib only. A brick only if it REPRODUCES the integers and the verdict does not flip:
running it must land the ratio band r_0/p^{1/phi(n)} inside the [0.77, 1.23] claimed in the
Lean file's docstring. (Measured here: ~[0.77, 1.23] for n=4 phi=2 and n=8 phi=4.)
"""
from math import comb, log
from collections import Counter
from itertools import product


def isprime(k):
    if k < 2:
        return False
    i = 2
    while i * i <= k:
        if k % i == 0:
            return False
        i += 1
    return True


def compositions(total, parts):
    """All nonneg integer tuples of length `parts` summing to `total`."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def E_char0_exact(n, r):
    """E_r over n-th roots of unity in C, EXACT (n a power of 2). The length-r sum with
    class-counts (k_0..k_{n-1}) equals the integer coordinate vector (k_j - k_{j+n/2}) in
    Z[zeta_n]; weight it by the multinomial and sum squared class counts."""
    half = n // 2
    classes = Counter()
    for ks in compositions(r, n):
        coord = tuple(ks[j] - ks[j + half] for j in range(half))
        mult, rem = 1, r
        for k in ks:
            mult *= comb(rem, k)
            rem -= k
        classes[coord] += mult
    return sum(c * c for c in classes.values())


def mu_Fp(n, p):
    def order(a):
        o, x = 1, a % p
        while x != 1:
            x = (x * a) % p
            o += 1
        return o
    g = 2
    while order(g) != p - 1:
        g += 1
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]


def E_charP_exact(mu, p, r):
    s = Counter()
    for x in product(mu, repeat=r):
        s[sum(x) % p] += 1
    return sum(c * c for c in s.values())


def onset_r0(n, p, rmax):
    mu = mu_Fp(n, p)
    for r in range(1, rmax + 1):
        if E_charP_exact(mu, p, r) != E_char0_exact(n, r):
            return r
    return None  # > rmax


def main():
    print("EXACT (no-float) cross-check of probe_onset_growth_law.py")
    print("onset r_0(n,p) vs the Minkowski/shortest-p-vector scale p^{1/phi(n)}")
    ratios = []
    for n, rmax, phi in [(4, 11, 2), (8, 8, 4)]:
        print(f"\n--- n={n} (phi={phi}) ---")
        print(f"{'p':>9}{'beta':>7}{'r_0':>6}{'p^(1/phi)':>11}{'r_0/p^(1/phi)':>15}")
        cnt, p = 0, n + 1
        while cnt < 8:
            if p % n == 1 and isprime(p):
                r0 = onset_r0(n, p, rmax)
                beta = log(p) / log(n)
                nb = p ** (1.0 / phi)
                if r0 is not None:
                    ratio = r0 / nb
                    ratios.append(ratio)
                    print(f"{p:>9}{beta:>7.2f}{r0:>6}{nb:>11.2f}{ratio:>15.3f}")
                else:
                    print(f"{p:>9}{beta:>7.2f}{'>'+str(rmax):>6}{nb:>11.2f}{'n/a':>15}")
                cnt += 1
                p += max(1, p // 3)
            p += 1
    if ratios:
        lo, hi = min(ratios), max(ratios)
        print(f"\nratio band (exact): [{lo:.3f}, {hi:.3f}]   claimed in _OnsetGrowthLaw.lean: [0.77, 1.23]")
        verdict = "REPRODUCED — float step was not corrupting the law" if lo >= 0.70 and hi <= 1.30 \
            else "MISMATCH — onset claim suspect"
        print(f"VERDICT: {verdict}")


if __name__ == "__main__":
    main()
