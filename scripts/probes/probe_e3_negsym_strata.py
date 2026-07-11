#!/usr/bin/env python3
"""probe_e3_negsym_strata.py  (#444)

Runnable witness for the negation-symmetric STRATA derivation of the exact 6th
energy moment E_3(mu_n) = 15 n^3 - 45 n^2 + 40 n (the sole open producer input of
the shipped r=2 rung CrossStepRungTwo.crossStepBound_two_of_exact_moments).

For PROPER smooth subgroups mu_n = <g^((p-1)/n)> of F_p* (n = 2^a, n | p-1, p large,
NEVER n = p-1), it checks three independent computations agree:
  1. E3_direct   = sum_s count3[s]^2,  count3[s] = #{(a,b,c) in mu_n^3 : a+b+c=s}
                 = rEnergy(mu_n,3) = #{(u,v) in mu_n^3 x mu_n^3 : sum u = sum v}.
  2. E3_strata   = 10n + (45n^2-90n) + (15n^3-90n^2+120n)  [partitions of 3]
                 = sum over shapes (3),(2,1),(1,1,1) of (#pair-choices)*(multinomial).
  3. E3_closed   = 15n^3 - 45n^2 + 40n.
and that the per-shape strata counts (computed from n only) sum to E3_direct.

Exit 0 iff all agree for every tested (n,p). This witnesses the kb note
docs/kb/e3-exact-via-negation-symmetric-strata.md (hand-algebra + this probe = two witnesses).
"""
import sys
from math import comb, isqrt

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i <= isqrt(m):
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo):
    """smallest prime p > lo with n | p-1 (so mu_n exists, proper since n < p-1)."""
    p = lo + (n - (lo % n)) + 1   # p ≡ 1 (mod n) candidate
    while p % n != 1 or not isprime(p):
        p += n
    return p

def gen_mu_n(p, n):
    """the order-n subgroup mu_n <= F_p*, as a sorted list of residues."""
    # a generator of F_p*: brute small g
    def order(g):
        x, k = g % p, 1
        while x != 1:
            x = (x * g) % p; k += 1
        return k
    g = 2
    while order(g) != p - 1:
        g += 1
    h = pow(g, (p - 1) // n, p)      # generator of mu_n
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x * h) % p
    assert len(set(S)) == n, "mu_n degenerate"
    assert sorted(S) != sorted(range(1, p)), "n = p-1 forbidden"
    return S

def e3_direct(p, n, S):
    """E_3 = sum_s count3[s]^2 over count3[s] = #{(a,b,c) in S^3 : a+b+c=s mod p}."""
    from collections import Counter
    c3 = Counter()
    for a in S:
        for b in S:
            ab = (a + b) % p
            for c in S:
                c3[(ab + c) % p] += 1
    return sum(v * v for v in c3.values())

def e3_strata(n):
    h = n // 2  # number of antipodal pairs (mu_n negation-closed, 0 not in mu_n, n even)
    s3   = h            * (720 // (6 * 6 // 1) if False else 20)   # 6!/(3!3!) = 20
    s21  = h * (h - 1)  * 180                                       # 6!/(2!2!) = 180
    s111 = comb(h, 3)   * 720                                       # 6!
    return s3, s21, s111

def main():
    cases = [(4, 10**4), (8, 10**5), (16, 10**6), (32, 10**8)]
    ok = True
    for n, lo in cases:
        p = find_prime(n, lo)
        S = gen_mu_n(p, n)
        closed = 15 * n**3 - 45 * n**2 + 40 * n
        s3, s21, s111 = e3_strata(n)
        strata = s3 + s21 + s111
        # direct enumeration only where n^3 is cheap (skip n=32: 32^3 fine actually)
        direct = e3_direct(p, n, S)
        match = (direct == closed == strata)
        ok = ok and match
        print(f"n={n:>3} p={p:>12}  E3_direct={direct:<14} closed={closed:<14} "
              f"strata={strata:<14} [{s3},{s21},{s111}]  {'OK' if match else 'MISMATCH'}")
    print("ALL MATCH" if ok else "FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
