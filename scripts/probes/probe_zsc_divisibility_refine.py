"""Probe: beyond 2 | zeroSumCount(mu_n, r), is there a STRONGER divisibility / structural law
on the thin mu_n that the global-negation parity alone misses? (#444 signed lane follow-on.)

mu_n is MULTIPLICATIVELY closed too (a subgroup), so beyond the additive global-negation Z/2
there is a multiplicative action: scaling all coords by g in mu_n permutes zero-sum tuples
(sum(g*t)=g*sum(t)=0). The DILATION group mu_n acts; combined with global negation (-1 in mu_n)
gives a (Z/2 x?) action. Question: does mu_n-dilation act FREELY on the NONDEGENERATE zero-sum
tuples (=> n | (zeroSumCount - degenerate))? Find the exact extra divisor.

Also tabulate zeroSumCount / 2 and gcd structure to find any clean law.
"""
import itertools
from math import gcd
from functools import reduce


def primes_one_mod_n(n, min_ratio=2, count=3):
    res = []
    k = 1
    while len(res) < count and k < n ** 3 + 5000:
        p = k * n + 1
        k += 1
        if p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)) and (p - 1) // n >= min_ratio:
            res.append(p)
    return res


def mun(n, p):
    for a in range(2, p):
        x = a % p
        kk = 1
        while x != 1 and kk <= p:
            x = (x * a) % p
            kk += 1
        if kk == n:
            S = []
            x = 1
            for _ in range(n):
                S.append(x)
                x = (x * a) % p
            return sorted(set(S)), a
    return None, None


def zerosum_tuples(S, p, r):
    return [t for t in itertools.product(S, repeat=r) if sum(t) % p == 0]


def main():
    print("zeroSumCount divisibility refinement on thin mu_n")
    print(f"{'n':>3} {'p':>6} {'r':>2} {'zsc':>7} {'zsc/2':>7} {'n|zsc?':>7} {'2n|zsc?':>8} {'gcd(zsc,n)':>11}")
    for n in [4, 8]:
        for p in primes_one_mod_n(n, count=2):
            S, g = mun(n, p)
            if S is None or len(S) != n:
                continue
            for r in [2, 3, 4, 5]:
                if n ** r > 4_000_000:
                    continue
                Z = zerosum_tuples(S, p, r)
                z = len(Z)
                print(f"{n:>3} {p:>6} {r:>2} {z:>7} {z//2 if z%2==0 else -1:>7} "
                      f"{str(z % n == 0):>7} {str(z % (2 * n) == 0):>8} {gcd(z, n):>11}")
    print()
    print("Interpretation: if 'n|zsc?' is NOT always True, the multiplicative dilation does NOT act")
    print("freely (degenerate tuples = fixed pts), so the clean extra divisor is just the global-")
    print("negation 2 (already proven). If '2n|zsc?' shows a pattern, there's a combined Z/2 x mu_n law.")


if __name__ == "__main__":
    main()
