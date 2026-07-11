#!/usr/bin/env python3
"""
#444 G1 — the S1 SCALING LAW (the actual quantity G1 must bound).

Findings so far:
  - descent identity exact; S1@global-argmax = 0 (even argmax) but mixed words TIE the even window
    with maxS1_mixed = 1 (single fibre) -> agreement still double-root-dominated.
The honest G1 question is NOT "is S1 empty" (it isn't: tying mixed words have S1=1) but:

   ** how large can S1 get, over ALL words reaching the beyond-Johnson window, as n grows? **

If max-over-window S1 is BOUNDED by an absolute constant (O(1), independent of n), then the
non-symmetric single-fibre correction adds at most O(1) to the list/agreement and the window-list
stays governed by the symmetric descent + O(1) => G1 closes (constant window). If max-window S1
GROWS with n, the non-symmetric term is a genuine extra contribution and G1 is open.

We measure, over weight-2 AND weight-3 words (sampled) that reach within the beyond-Johnson window
(agreement >= Johnson-ish threshold t*(n)):
  - max S1 among window-reaching words,
  - the (S1>0)-word count,
  - max single-fibre root count over mixed words.

Honest: EXACT mod p, proper 2-power mu_n, p>>n^3, structured primes, never n=q-1. Probe only.
"""
from sympy import isprime, primitive_root
import random


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
    return [pow(h, j, p) for j in range(n)], h


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


def descent_terms(P, Q, muN, p):
    double, S1 = 0, 0
    for y in muN:
        Pv = evalpoly(P, y, p)
        Qv = evalpoly(Q, y, p)
        if Pv == 0 and Qv == 0:
            double += 1
        elif Qv != 0 and (Pv * Pv) % p == (y * Qv * Qv) % p:
            S1 += 1
    return double, S1


def main():
    print("=" * 78)
    print("#444 G1 — S1 scaling law over beyond-Johnson window words")
    print("=" * 78)
    # Johnson radius for RS[n,k]: agreement threshold ~ sqrt(k*n). We use k = rate*n.
    # window = agreement in (Johnson, ...]; we just report max S1 among the TOP agreement words.
    print(f"  {'n':>4} {'p':>12} {'k':>4} {'topAgr':>7} {'maxS1_window':>13} {'#S1>0_window':>13} {'maxS1_all':>10}")
    fc = {}
    for n in [8, 16, 32, 64]:
        p = find_prime(n, beta=4)
        mun, h = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        F0, G0 = split_even_odd(fc)
        k = max(2, n // 4)  # low rate -> large beyond-Johnson window
        # enumerate weight-2 + sample weight-3 words
        words = []
        for a in range(n):
            for b in range(a + 1, n):
                words.append({a: 1, b: 1})
        # sample weight-3 words
        random.seed(3)
        for _ in range(min(3000, n * n)):
            es = random.sample(range(n), 3)
            words.append({e: 1 for e in es})
        results = []
        max_s1_all = 0
        for uc in words:
            ue, uo = split_even_odd(uc)
            P = {e: (F0.get(e, 0) - ue.get(e, 0)) % p for e in set(F0) | set(ue)}
            Q = {e: (G0.get(e, 0) - uo.get(e, 0)) % p for e in set(G0) | set(uo)}
            dbl, s1 = descent_terms(P, Q, muN, p)
            agr = 2 * dbl + s1
            results.append((agr, s1))
            if s1 > max_s1_all:
                max_s1_all = s1
        top = max(a for a, _ in results)
        # window = top quartile of agreement (beyond-Johnson-ish), Johnson ~ sqrt(k*n)
        import math
        johnson = math.sqrt(k * n)
        window = [(a, s1) for (a, s1) in results if a > johnson]
        maxS1_win = max((s1 for _, s1 in window), default=0)
        nS1_win = sum(1 for _, s1 in window if s1 > 0)
        print(f"  {n:>4} {p:>12} {k:>4} {top:>7} {maxS1_win:>13} {nS1_win:>13} {max_s1_all:>10}")

    print("\nINTERPRETATION:")
    print(" maxS1_window BOUNDED (O(1), flat in n) => non-symmetric single-fibre correction adds")
    print("   at most a constant to the beyond-Johnson agreement; G1 window-list stays constant")
    print("   modulo O(1) => the symmetric descent governs, S1 is strict sub-leading. ATTACKABLE")
    print("   as a constraint lemma 'S1 <= const'. If maxS1_window GROWS in n => G1 genuinely open.")


if __name__ == "__main__":
    main()
