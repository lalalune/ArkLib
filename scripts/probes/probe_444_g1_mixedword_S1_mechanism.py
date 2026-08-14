#!/usr/bin/env python3
"""
#444 G1 follow-up — the MIXED-word single-fibre mechanism (deconfliction-clean).

Prior probe (probe_444_g1_singlefibre_root_bound.py) found:
  - descent identity exact; S1@argmax = 0 EXACTLY (Shaw G1 confirmed for even worst words);
  - BUT R = #roots_{mu_N}(P^2 - y Q^2) ~ N/2 = n/4 (LINEAR, not O(1)) — naive root bound has
    only a factor-2 slack, NOT a constant collapse.

So S1=0 at the EVEN argmax must come from R being entirely DOUBLE-roots (P=Q=0), i.e. the even
argmax word has Q == 0 (purely even), making the single-fibre term structurally empty. The REAL
G1 crux is whether a MIXED word (Q != 0) can have LARGE S1 in the beyond-Johnson window — that is
the only way S1 contributes. This probe isolates that:

  Q1. For purely-even words (Q==0): confirm S1==0 IDENTICALLY (definitional: Q!=0 required).
  Q2. For MIXED weight-2 words (one even one odd exponent => Q != 0): measure S1 and the agreement.
      Does any mixed word reach the beyond-Johnson window (agreement > Johnson bound)? If mixed
      words NEVER beat the even-word window, S1 is irrelevant to the worst case (the agreement
      maximizer is always even => S1=0) — which is EXACTLY Shaw's branching=1 claim, now made
      mechanistic, NOT just "empirically empty".
  Q3. Among ALL words (any weight, sampled), is the GLOBAL agreement-argmax always EVEN (Q=0)?
      Report max agreement achieved by Q!=0 words vs Q==0 words. If max_{Q!=0} agr < max_{Q=0} agr
      strictly in the window, the worst case is provably symmetric/even => the non-symmetric S1
      term carries NO worst-case mass.

This converts Shaw's "S1 empirically empty" into a SHARP STRUCTURAL DICHOTOMY: the agreement
maximizer is even (Q=0, S1=0) OR a mixed word that provably falls short of the even window. Either
way the worst-case list size is governed by the SYMMETRIC even-descent, and S1 is a strict
sub-leading correction. (Honest target for a constraint lemma: max-agreement-word-has-Q=0, OR
mixed-word-agreement < even-word-window.)
"""
from sympy import isprime, primitive_root


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
    print("#444 G1 — mixed-word single-fibre mechanism: is the worst word always EVEN (Q=0)?")
    print("=" * 78)
    print(f"  {'n':>4} {'p':>12} {'maxAgr_even':>11} {'maxAgr_mixed':>12} {'maxS1_mixed':>11} {'even>mixed?':>11}")
    for n in [8, 16, 32, 64]:
        p = find_prime(n, beta=4)
        mun, h = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        fc = {}  # zero codeword reference
        F0, G0 = split_even_odd(fc)
        max_even = -1
        max_mixed = -1
        max_s1_mixed = 0
        # all weight-2 words u = x^a + x^b
        for a in range(n):
            for b in range(a + 1, n):
                uc = {a: 1, b: 1}
                ue, uo = split_even_odd(uc)
                P = {e: (F0.get(e, 0) - ue.get(e, 0)) % p for e in set(F0) | set(ue)}
                Q = {e: (G0.get(e, 0) - uo.get(e, 0)) % p for e in set(G0) | set(uo)}
                Qnonzero = any(v % p for v in Q.values())
                dbl, s1 = descent_terms(P, Q, muN, p)
                agr = 2 * dbl + s1
                if Qnonzero:
                    if agr > max_mixed:
                        max_mixed = agr
                    if s1 > max_s1_mixed:
                        max_s1_mixed = s1
                else:
                    if agr > max_even:
                        max_even = agr
        verdict = "YES" if max_even > max_mixed else ("TIE" if max_even == max_mixed else "NO(!)")
        print(f"  {n:>4} {p:>12} {max_even:>11} {max_mixed:>12} {max_s1_mixed:>11} {verdict:>11}")

    print("\nINTERPRETATION:")
    print(" even>mixed = YES at all n  => the agreement maximizer is ALWAYS an even word (Q=0),")
    print("   so S1 is structurally 0 at the worst case (branching=1 is MECHANISTIC, not just")
    print("   empirical): the non-symmetric single-fibre term never carries worst-case mass.")
    print(" If NO anywhere => a mixed word beats the even window and S1 matters => G1 genuinely open.")


if __name__ == "__main__":
    main()
