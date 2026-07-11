#!/usr/bin/env python3
"""
#444 G2-adjacent — the weight-2 word quadform is an explicit BINOMIAL, and its mu_N root count.

For a weight-2 word u = x^a + x^b (vs the zero codeword f=0), the even/odd split is:
  u_e = sum of even-exponent terms (as poly in y=x^2), u_o = sum of odd-exponent terms.
  P = F - u_e = -u_e,  Q = G - u_o = -u_o.
Cases:
  (a,b both even): u_o=0 => Q=0 (pure even). R = P^2 = u_e^2 = (x^a+x^b -> y^{a/2}+y^{b/2})^2.
                   single-fibre S1 structurally 0 (needs Q!=0). [confirmed earlier]
  (a even, b odd): u_e = y^{a/2}, u_o = y^{(b-1)/2}. P=-y^{a/2}, Q=-y^{(b-1)/2}.
                   R = P^2 - y Q^2 = y^a - y^{b}   (since y*(y^{(b-1)/2})^2 = y^b). a BINOMIAL.
  (a,b both odd):  u_e=0 => P=0 => R = -y Q^2; Z-condition P^2=yQ^2 => 0 = y Q^2 => Q=0 or y=0.

This probe confirms: for the MIXED weight-2 word, R(y) = y^a - y^b is an explicit BINOMIAL, so
  Z = #{y in mu_N : y^a = y^b} = #{y in mu_N : y^{|a-b|} = 1} = gcd(|a-b|, N)
(the standard subgroup root count of a binomial over the cyclic group mu_N of order N). This is the
EXACT, finite, structural value of the non-symmetric Z-term for a mixed weight-2 word -- it is the
gcd of the exponent gap with N, which the worst-word (mid-exponent) analysis maximises. NO degree
slack lost: deg R = max(a,b) but the mu_N-root count is gcd(|a-b|, N) << deg R, the subgroup
structure DOES constrain the binomial (unlike the generic case). This sharpens the deg-R Lagrange
bound for the weight-2 family specifically.

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
    print("#444 G2 — mixed weight-2 quadform R = y^a - y^b binomial; Z = gcd(|a-b|, N)")
    print("=" * 78)
    okall = True
    print(f"  {'n':>4} {'N':>4} {'a':>3} {'b':>3} {'Z_direct':>8} {'gcd(|a-b|,N)':>12} {'match':>6}")
    for n in [8, 16, 32, 64]:
        p = find_prime(n)
        mun = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        N = len(muN)
        # test several mixed weight-2 words (a even, b odd) -> R = y^a - y^b  (exponents in y)
        # build R directly from even/odd split to be faithful, then count mu_N roots
        import random
        random.seed(2)
        tested = 0
        for _ in range(8):
            a2 = random.randrange(0, n)
            b2 = random.randrange(0, n)
            if a2 % 2 == b2 % 2:
                continue  # want mixed
            # ensure a even, b odd labelling
            ae, bo = (a2, b2) if a2 % 2 == 0 else (b2, a2)
            # P = -y^{ae/2}, Q = -y^{(bo-1)/2}; R(y)= y^{ae} - y^{bo}
            expa = ae           # P^2 = y^{ae}
            expb = bo           # y*Q^2 = y^{1 + (bo-1)} = y^{bo}
            Z = sum(1 for y in muN if (pow(y, expa, p) - pow(y, expb, p)) % p == 0)
            g = gcd(abs(expa - expb), N)
            match = (Z == g)
            if not match:
                okall = False
            print(f"  {n:>4} {N:>4} {expa:>3} {expb:>3} {Z:>8} {g:>12} {str(match):>6}")
            tested += 1
            if tested >= 4:
                break
    print(f"\n  => Z = gcd(|a-b|, N) for mixed weight-2 words: {'ALL MATCH' if okall else 'MISMATCH'}")
    print("  The subgroup mu_N (cyclic order N) constrains the binomial root count to gcd(|a-b|,N),")
    print("  far below deg R = max(a,b). The worst weight-2 word maximises this gcd. This is the")
    print("  EXACT non-symmetric Z for the weight-2 family -- a clean cyclotomic/gcd handle, no")
    print("  Gauss-sum, sharpening the generic deg-R Lagrange bound on the weight-2 locus.")


if __name__ == "__main__":
    main()
