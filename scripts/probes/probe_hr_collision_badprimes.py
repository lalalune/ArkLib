#!/usr/bin/env python3
"""
probe_hr_collision_badprimes.py  (#444)  — corroborates the F7 good-prime collision residual,
and locates the good/bad-prime crossover (= the BGK p-dependence boundary).

Honest frontier (after the complete-homogeneous SPECTRUM route was refuted as a δ* pin — it is
exponentially loose for #bad, §D4): the forced-γ values γ_R = −h_{a−k}(R)/h_{b−k}(R), equivalently the
complete-homogeneous values h_r(R), live in ℤ[ζ_s]. Two char-0-DISTINCT values collide mod p ⟺
p | Norm(difference). The good-prime question (F4 Linnik) needs a prime p = Θ(n^β) (β≈4) where the
char-0-distinct values stay DISTINCT mod p. The COMBINATORIAL half (landable, F7) is that the BAD
primes are FINITE (bounded by resultant/norm divisors); the quantitative EXISTENCE at polynomial size
is the named analytic residual (effective Linnik / PNT-in-AP).

This probe measures the crossover directly. For each (s, r) at rate ρ=1/4 (k+1 = s/4+1):
  D0              = #distinct h_r(R) over (k+1)-subsets in char 0 (via a very large prime surrogate),
  first_good_prime= smallest prime p ≡ 1 (mod s) with #distinct h_r mod p == D0 (no collision),
  ratio           = first_good_prime / n^4   (n^4 = the prize field scale q = Θ(n^β), β≈4).

FINDINGS (this script): good primes EXIST below n^4 at all tested s (combinatorial half holds), BUT
the ratio first_good/n^4 CLIMBS sharply (s=8: ~0.004, s=16: ~0.3–0.4) as the spectrum D0 grows
(exponentially). That climb IS the good/bad-prime crossover = the BGK p-dependence wall: whether
first_good stays < n^β as n→∞ is the open analytic residual, and the climbing ratio shows it sits
right at the boundary. So F7's combinatorial finiteness is real and landable; the QUANTITATIVE good
prime at polynomial size is the genuine wall (consistent with memory issue407: good/bad crossover =
BGK p-dependence). NOT a closure.
"""
import itertools
from math import comb

def isprime(x):
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return x > 1

def primes_1_mod_s(s, count, lo=2):
    out = []
    p = max(lo, s + 1)
    while len(out) < count:
        if p % s == 1 and isprime(p):
            out.append(p)
        p += 1
    return out

def subgroup(s, p):
    for g in range(2, p):
        h = pow(g, (p - 1) // s, p)
        if pow(h, s, p) == 1 and all(pow(h, s // q, p) != 1 for q in [2] if s % q == 0):
            return [pow(h, i, p) for i in range(s)]
    return None

def hsym(R, r, p):
    dp = [0] * (r + 1); dp[0] = 1
    for x in R:
        ndp = dp[:]
        for j in range(1, r + 1):
            ndp[j] = (dp[j] + x * ndp[j - 1]) % p
        dp = ndp
    return dp[r]

def distinct(s, r, p, k):
    S = subgroup(s, p)
    return len({hsym(R, r, p) for R in itertools.combinations(S, k + 1)})

def main():
    print("F7 corroboration — good/bad-prime crossover for the h_r values (= BGK p-dependence boundary).")
    print(f"{'s':>3}{'r':>3}{'k+1':>4} | {'D0(char0)':>9} {'first_good_p':>12} {'#bad_before':>11} "
          f"{'n^4':>8} {'ratio':>7} {'<n^4?':>6}")
    print("-" * 72)
    for s in (8, 12, 16):
        k = s // 4
        big = primes_1_mod_s(s, 1, lo=10 ** 7)[0]
        for r in (2, 3, 4):
            D0 = distinct(s, r, big, k)
            first_good, nbad = None, 0
            for p in primes_1_mod_s(s, 6000):
                if distinct(s, r, p, k) == D0:
                    first_good = p
                    break
                nbad += 1
            n4 = s ** 4
            ratio = (first_good / n4) if first_good else float('inf')
            tag = "yes" if first_good and first_good < n4 else "NO"
            fg = first_good if first_good else ">scan"
            print(f"{s:>3}{r:>3}{k+1:>4} | {D0:>9} {str(fg):>12} {nbad:>11} {n4:>8} {ratio:>7.3f} {tag:>6}")
    print()
    print("Reading: good primes exist < n^4 (F7 combinatorial half holds), but ratio first_good/n^4")
    print("CLIMBS with the (exponentially growing) spectrum D0 — the good/bad crossover = BGK wall.")
    print("Quantitative good-prime existence at n^β as n→∞ = the open analytic Linnik residual.")

if __name__ == "__main__":
    main()
