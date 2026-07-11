#!/usr/bin/env python3
"""
#444 list-decoding SEAM A (even/odd non-symmetric dyadic descent) — G1 probe.

Shaw's essay (2026-06-15, top of #444) localized the list-decoding side to an axiom-clean
descent identity:
    |agreement(f,u)| = 2*#{y in mu_N : P(y)=Q(y)=0}  +  #{y in mu_N : Q(y)!=0 and P(y)^2 = y*Q(y)^2}
where for mu_n c F_p^* with n=2N, squaring pi: x|->y=x^2 (fibre {x,-x}),
f(x)=F(x^2)+x G(x^2), u(x)=u_e(x^2)+x u_o(x^2), P=F-u_e, Q=G-u_o.

The SECOND term is the NON-SYMMETRIC single-fibre correction S1:
    S1(P,Q) := #{ y in mu_N : Q(y) != 0 and P(y)^2 = y * Q(y)^2 }.

Shaw's open gap G1: at the worst LARGE-agreement words, S1 is *empirically EMPTY*, but the
a-priori degree bound on #roots_{mu_N}(P^2 - y Q^2) is too loose. The genuine technical crux is
a SHARPER SUBGROUP-ROOT BOUND on the count
    R(P,Q) := #{ y in mu_N : P(y)^2 - y*Q(y)^2 = 0 }   (= S1 plus the P=Q=0 double-roots).

THIS PROBE (deconflicted: no probe_444_monomial_descent / worstword exists in-tree; the G1 root
count itself has NEVER been directly probed). It asks the finite, computable questions the gap raises:

  Q1. SANITY: verify the descent identity on random (f,u) over proper mu_n, p>>n^3. (must be exact)
  Q2. WORST-WORD S1: at the binding large-agreement word (weight-2 even word x^a+x^b that maximizes
      agreement in the beyond-Johnson window), is S1 == 0 EXACTLY? (Shaw: yes, empirically)
  Q3. THE ROOT BOUND R(P,Q): how does #roots_{mu_N}(P^2 - y Q^2) actually scale? The naive bound is
      deg = 2*max(degP, degQ)+1 (could be ~n). The CLAIM that makes G1 work is that for the relevant
      P,Q (differences of LOW-degree codeword parts) R is BOUNDED (constant / O(1)), NOT ~n. Measure
      R over the worst words across n=8..128, multiple structured primes. Is R = O(1)? what bounds it?
  Q4. MECHANISM: when Q != 0, P^2 = y Q^2 means y = (P/Q)^2 is a SQUARE in F_p; but y ranges over
      mu_N which (n=2N, N=2^{a-1}) is itself the squares-coset structure. Does the constraint
      "y must be BOTH in mu_N AND a perfect square (P/Q)^2" force R small via a subgroup-intersection
      count? Probe the size of { y in mu_N : y is a square in F_p and y=(P/Q(y))^2 consistently }.

Honesty: probe-first, EXACT arithmetic mod p, PROPER 2-power mu_n, p>>n^3, structured + generic
primes, m=(p-1)/n>1, NEVER n=q-1. No formalization here; this characterizes the object so a real
subgroup-root constraint lemma (or an honest wall) can be written.
"""
import sys
from sympy import isprime, primitive_root, factorint


def find_prime(n, beta=4, want_struct=True):
    """p = k*2^a + 1 (FFT/structured) with p > n^beta, mu_n a PROPER subgroup."""
    a = n.bit_length() - 1  # n = 2^a
    assert (1 << a) == n, f"n must be 2-power, got {n}"
    target = n ** beta
    # k odd, p = k*2^mu + 1, mu >= a so n | p-1; p proper => m=(p-1)/n>1
    mu = a + 3
    while True:
        base = 1 << mu
        k = (target // base) | 1  # odd
        for _ in range(20000):
            p = k * base + 1
            if p > target and isprime(p) and (p - 1) % n == 0 and (p - 1) // n > 1:
                return p
            k += 2
        mu += 1


def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    mu = [pow(h, j, p) for j in range(n)]
    return mu, h


def is_square_mod(a, p):
    if a % p == 0:
        return True
    return pow(a % p, (p - 1) // 2, p) == 1


def evalpoly(coeffs, y, p):
    """coeffs is dict exp->coef; eval at y mod p."""
    s = 0
    for e, c in coeffs.items():
        s = (s + c * pow(y, e, p)) % p
    return s


def agreement_bruteforce(fcoeffs, ucoeffs, mun, p):
    """#{x in mu_n : f(x) == u(x)}."""
    cnt = 0
    for x in mun:
        if evalpoly(fcoeffs, x, p) == evalpoly(ucoeffs, x, p):
            cnt += 1
    return cnt


def split_even_odd(coeffs):
    """f(x)=F(x^2)+x G(x^2). Return F,G as exp(in y)->coef dicts."""
    F, G = {}, {}
    for e, c in coeffs.items():
        if e % 2 == 0:
            F[e // 2] = (F.get(e // 2, 0) + c)
        else:
            G[(e - 1) // 2] = (G.get((e - 1) // 2, 0) + c)
    return F, G


def descent_terms(P, Q, muN, p):
    """Return (double, S1) where double=#{y:P=Q=0}, S1=#{y:Q!=0 and P^2=yQ^2}."""
    double = 0
    S1 = 0
    for y in muN:
        Pv = evalpoly(P, y, p)
        Qv = evalpoly(Q, y, p)
        if Pv == 0 and Qv == 0:
            double += 1
        elif Qv != 0 and (Pv * Pv) % p == (y * (Qv * Qv)) % p:
            S1 += 1
    return double, S1


def root_count_P2_yQ2(P, Q, muN, p):
    """R = #{y in muN : P(y)^2 - y Q(y)^2 = 0} (= double-roots + S1-roots)."""
    R = 0
    for y in muN:
        Pv = evalpoly(P, y, p)
        Qv = evalpoly(Q, y, p)
        if (Pv * Pv - y * Qv * Qv) % p == 0:
            R += 1
    return R


def main():
    print("=" * 78)
    print("#444 G1: single-fibre correction S1 and the subgroup-root bound R(P^2-yQ^2)")
    print("=" * 78)

    # ---- Q1 SANITY: descent identity on random (f,u) ----
    print("\n[Q1] descent identity sanity (random low-degree f,u over proper mu_n):")
    import random
    random.seed(1)
    ok = True
    for n in [8, 16, 32]:
        p = find_prime(n, beta=4)
        mun, h = subgroup(p, n)
        muN = [pow(x, 2, p) for x in mun]  # squaring image; dedup
        muN = sorted(set(muN))
        for _ in range(40):
            deg = n // 2
            fc = {e: random.randrange(p) for e in range(deg)}
            uc = {e: random.randrange(p) for e in range(deg)}
            F, G = split_even_odd(fc)
            ue, uo = split_even_odd(uc)
            P = {e: (F.get(e, 0) - ue.get(e, 0)) % p for e in set(F) | set(ue)}
            Q = {e: (G.get(e, 0) - uo.get(e, 0)) % p for e in set(G) | set(uo)}
            agr = agreement_bruteforce(fc, uc, mun, p)
            dbl, s1 = descent_terms(P, Q, muN, p)
            if agr != 2 * dbl + s1:
                ok = False
                print(f"   MISMATCH n={n}: agr={agr} 2*dbl+s1={2*dbl+s1}")
                break
        print(f"   n={n:>3} p={p:>12}  identity holds on 40 trials: {ok}")
        if not ok:
            break
    print(f"   => Q1 {'PASS (identity exact)' if ok else 'FAIL'}")

    # ---- Q2/Q3/Q4: worst weight-2 even word, S1 and R scaling ----
    # Worst even word family: x^a + x^b, both even (even word), beyond-Johnson window.
    # We scan even weight-2 words u(x) = x^a + x^b vs codeword f, and measure S1, R at the
    # word that MAXIMIZES agreement (the binding word). To stay honest+finite we take f as the
    # zero codeword's window: i.e. measure for the bare difference object P,Q induced by
    # weight-2 EVEN words directly (P from even part, Q=0 when word is purely even -> S1 trivially
    # 0). So the NON-trivial S1 needs a MIXED word. We therefore scan general weight-2 words
    # u=x^a+x^b over ALL (a,b) and report the MAX S1 and MAX R, plus whether the agreement-maximizer
    # has S1=0.
    print("\n[Q2/Q3/Q4] worst weight-2 word: max S1, max R, and S1 at the agreement-argmax")
    print(f"  {'n':>4} {'p':>12} {'maxAgr':>7} {'S1@argmax':>10} {'maxS1':>6} {'maxR':>5} {'R/n':>6} {'naiveDeg':>9}")
    for n in [8, 16, 32, 64, 128]:
        p = find_prime(n, beta=4)
        mun, h = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        Nlen = len(muN)
        # f = a fixed low-degree codeword (degree < k); use f=0 codeword window relative to words.
        # Scan weight-2 words u = x^a + x^b, 0<=a<b<n. agreement vs f=0 codeword (P from -u_e etc).
        fc = {}  # zero codeword
        best_agr = -1
        best_s1 = None
        max_s1 = 0
        max_R = 0
        # cap the scan for large n
        pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
        if len(pairs) > 4000:
            random.seed(7)
            pairs = random.sample(pairs, 4000)
        for (a, b) in pairs:
            uc = {a: 1, b: 1}
            F, G = split_even_odd(fc)
            ue, uo = split_even_odd(uc)
            P = {e: (F.get(e, 0) - ue.get(e, 0)) % p for e in set(F) | set(ue)}
            Q = {e: (G.get(e, 0) - uo.get(e, 0)) % p for e in set(G) | set(uo)}
            dbl, s1 = descent_terms(P, Q, muN, p)
            agr = 2 * dbl + s1
            R = root_count_P2_yQ2(P, Q, muN, p)
            if s1 > max_s1:
                max_s1 = s1
            if R > max_R:
                max_R = R
            if agr > best_agr:
                best_agr = agr
                best_s1 = s1
        naive = 2 * (n // 2) + 1  # naive root-bound deg of P^2 - yQ^2
        print(f"  {n:>4} {p:>12} {best_agr:>7} {best_s1:>10} {max_s1:>6} {max_R:>5} {max_R/Nlen:>6.2f} {naive:>9}")

    print("\nINTERPRETATION:")
    print(" - S1@argmax: is the single-fibre correction EMPTY (0) at the agreement-maximizing word?")
    print("   (Shaw's G1 empirical claim: yes for even worst words.)")
    print(" - maxR vs naiveDeg: if maxR stays O(1)/bounded while naiveDeg ~ n, the subgroup-root")
    print("   bound has REAL slack a sharper lemma could grip => G1 attackable. If maxR ~ n, the")
    print("   root count is NOT subgroup-constrained and G1's crux is genuinely hard.")


if __name__ == "__main__":
    main()
