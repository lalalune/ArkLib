#!/usr/bin/env python3
"""
#444 G2 — the EVEN-EVEN weight-2 spine count A = #{y in mu_N : y^c = -1}.

Companion to the mixed weight-2 result (Z = gcd(|a-b|, N)). For an EVEN-EVEN weight-2 word
u = x^a + x^b (a,b both even, vs zero codeword), the even/odd split gives u_o = 0 => Q = 0, so
the non-symmetric Z = 0 (S1 needs Q!=0). The agreement is the pure SYMMETRIC spine:
  agreement = 2*A,  A = #{y in mu_N : P(y) = 0},  P = -(y^{a/2} + y^{b/2}).
So A = #{y in mu_N : y^{a/2} + y^{b/2} = 0} = #{y in mu_N : y^{(a/2 - b/2)} = -1}  (factor y^{b/2}).

This is a COSET-SHIFTED binomial root count: solutions to y^c = -1 in the cyclic group mu_N
(c = |a-b|/2). Over a cyclic group of order N, #{y : y^c = -1} is either 0 (if -1 not in the
image of the c-power map) or gcd(c, N) (a full kernel-coset). Specifically it equals gcd(c,N)
iff -1 is a c-th power, i.e. iff the order of -1 (which is 2, when N even) divides N/gcd(c,N).

This probe measures A directly and checks A in {0, gcd(c,N)}, and WHEN it is gcd(c,N) vs 0. This
is the EXACT even-even weight-2 spine list size -- the symmetric companion to the mixed gcd result,
completing the weight-2 agreement census (mixed: 2A'+1-style via Z; even-even: 2A pure spine).

probe-first: EXACT mod p, proper 2-power mu_n, p>>n^3, structured primes, never n=q-1.
"""
from sympy import isprime, primitive_root
from math import gcd


def find_prime(n, beta=4):
    a = n.bit_length() - 1
    target = n ** beta
    mu = a + 3
    while True:
        base = 1 << mu
        k = (target // base) | 1
        for _ in range(20000):
            p = k * base + 1
            if p > target and isprime(p) and (p - 1) % n == 0 and (p - 1) // n > 1:
                return p
            k += 2
        mu += 1


def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]


def main():
    print("=" * 78)
    print("#444 G2 — even-even weight-2 spine A = #{y in mu_N : y^c = -1}, c=|a-b|/2")
    print("=" * 78)
    okall = True
    print(f"  {'n':>4} {'N':>4} {'a':>3} {'b':>3} {'c':>4} {'A_direct':>8} {'gcd(c,N)':>8} {'A in{0,gcd}':>11} {'-1 cpow?':>8}")
    import random
    random.seed(5)
    for n in [8, 16, 32, 64]:
        p = find_prime(n)
        mun = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        N = len(muN)
        tested = 0
        for _ in range(20):
            a2 = 2 * random.randrange(0, n // 2)
            b2 = 2 * random.randrange(0, n // 2)
            if a2 == b2:
                continue
            c = abs(a2 - b2) // 2
            # P(y) = -(y^{a/2} + y^{b/2}); A = #{y in muN : y^{a/2}+y^{b/2}=0}
            A = sum(1 for y in muN
                    if (pow(y, a2 // 2, p) + pow(y, b2 // 2, p)) % p == 0)
            g = gcd(c, N)
            in_set = A in (0, g)
            # is -1 a c-th power in muN? i.e. does some y have y^c = -1
            neg1_is_cpow = any(pow(y, c, p) == (p - 1) for y in muN)
            if not in_set:
                okall = False
            print(f"  {n:>4} {N:>4} {a2:>3} {b2:>3} {c:>4} {A:>8} {g:>8} {str(in_set):>11} {str(neg1_is_cpow):>8}")
            tested += 1
            if tested >= 4:
                break
    print(f"\n  => even-even spine A in {{0, gcd(c,N)}}: {'ALL MATCH' if okall else 'MISMATCH'}")
    print("  A = gcd(c,N) exactly when -1 is a c-th power in mu_N, else 0. The exact even-even")
    print("  weight-2 spine count -- a coset-shifted binomial root count, completing the weight-2")
    print("  census alongside the mixed-word Z = gcd(|a-b|,N). NON-moment, cyclotomic.")


if __name__ == "__main__":
    main()
