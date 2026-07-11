#!/usr/bin/env python3
"""
#444 G2 — does a WEIGHT-3 word ever beat the weight-2 beyond-Johnson window? (the G2 minimality crux)

Shaw's essay claims (verified, not proven): worst-over-ALL-words is weight-2; a full weight-3/weight-4
enumeration never beats the weight-2 worst and never grows faster in n. My weight-2 census is now
locked (mixed Z=gcd(|a-b|,N); even-even spine A<=gcd(c,N)). The remaining G2 gap is MINIMALITY: no
higher-weight word beats weight-2 in the window.

This probe stress-tests the weight-3 case directly: enumerate weight-3 words u = x^a+x^b+x^c (vs zero
codeword), compute the FULL agreement = 2A + Z over mu_n, and compare the MAX weight-3 agreement to
the MAX weight-2 agreement, specifically in the beyond-Johnson window (agreement > sqrt(k*n)).

Q1. max weight-3 agreement vs max weight-2 agreement (overall + in window).
Q2. does any weight-3 word STRICTLY beat the weight-2 max in the window? (if never => G2 minimality
    holds empirically at weight 3, consistent with Shaw; if sometimes => the claim is more subtle).
Q3. for weight-3, is Z still degree/gcd-controlled (R = P^2 - yQ^2 with P,Q now BINOMIALS, deg<=2
    in each => deg R <= 5)? Report max Z weight-3 vs the deg bound.

probe-first: EXACT mod p, proper 2-power mu_n, p>>n^3, structured primes, never n=q-1.
"""
from sympy import isprime, primitive_root
import math, itertools


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


def evalpoly(coeffs, y, p):
    s = 0
    for e, c in coeffs.items():
        s = (s + c * pow(y, e, p)) % p
    return s % p


def split_even_odd(coeffs):
    F, G = {}, {}
    for e, c in coeffs.items():
        if e % 2 == 0:
            F[e // 2] = (F.get(e // 2, 0) + c)
        else:
            G[(e - 1) // 2] = (G.get((e - 1) // 2, 0) + c)
    return F, G


def descent_AZ(uc, muN, p):
    F0, G0 = {}, {}  # zero codeword
    ue, uo = split_even_odd(uc)
    P = {e: (-ue.get(e, 0)) % p for e in ue}
    Q = {e: (-uo.get(e, 0)) % p for e in uo}
    A = 0
    Z = 0
    for y in muN:
        Pv = evalpoly(P, y, p) if P else 0
        Qv = evalpoly(Q, y, p) if Q else 0
        if Pv == 0 and Qv == 0:
            A += 1
        elif (Pv * Pv) % p == (y * Qv * Qv) % p:
            Z += 1
    return A, Z, 2 * A + Z


def main():
    print("=" * 78)
    print("#444 G2 — weight-3 vs weight-2 beyond-Johnson window (minimality crux)")
    print("=" * 78)
    print(f"  {'n':>4} {'p':>12} {'k':>3} {'maxAgr_w2':>9} {'maxAgr_w3':>9} {'w3>w2_win?':>10} {'maxZ_w3':>7} {'degR<=5':>7}")
    any_w3_beats = False
    for n in [8, 16, 32]:
        p = find_prime(n)
        mun = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        k = max(2, n // 4)
        johnson = math.sqrt(k * n)
        # weight-2
        maxw2 = -1
        for a in range(n):
            for b in range(a + 1, n):
                _, _, agr = descent_AZ({a: 1, b: 1}, muN, p)
                if agr > maxw2:
                    maxw2 = agr
        # weight-3 (full enum for small n, sample for n=32)
        maxw3 = -1
        maxZ3 = 0
        triples = list(itertools.combinations(range(n), 3))
        if len(triples) > 6000:
            import random
            random.seed(9)
            triples = random.sample(triples, 6000)
        w3_win_beats = False
        for (a, b, c) in triples:
            A, Z, agr = descent_AZ({a: 1, b: 1, c: 1}, muN, p)
            if agr > maxw3:
                maxw3 = agr
            if Z > maxZ3:
                maxZ3 = Z
            if agr > johnson and agr > maxw2:
                w3_win_beats = True
                any_w3_beats = True
        degRok = maxZ3 <= 5
        print(f"  {n:>4} {p:>12} {k:>3} {maxw2:>9} {maxw3:>9} {str(w3_win_beats):>10} {maxZ3:>7} {str(degRok):>7}")
    print(f"\n  => any weight-3 word beats weight-2 in window: {any_w3_beats}")
    print("  False everywhere => G2 minimality holds empirically at weight 3 (Shaw's claim), the")
    print("  weight-2 census (mixed gcd + even-even spine) governs the worst case. maxZ_w3<=5")
    print("  confirms weight-3 Z stays degree-controlled (R=P^2-yQ^2, P,Q binomials => deg R<=5).")


if __name__ == "__main__":
    main()
