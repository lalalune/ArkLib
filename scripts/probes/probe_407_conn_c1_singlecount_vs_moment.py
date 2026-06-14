#!/usr/bin/env python3
"""
#407 CONNECTION C1 — does the bad-scalar COUNT genuinely bypass the BGK deep-moment wall?

The task: make rigorous the claim "the COUNT bypasses the BGK deep-moment wall because it is a
single-r quantity."  This is a CLAIM under suspicion: the KB itself records (line 704-711) that
the count of GAP-VALID CONFIGS is (1/p^2) sum_{a,b} S(a,b)^{2r} = a 2r-th MOMENT, hence re-hits
BGK.  We must separate two genuinely different objects and decide which one delta* depends on.

Two objects, n = 2^mu, p prime, p == 1 mod n, mu_n = order-n subgroup of F_p^*:
  (A) bad-scalar count  N0 := | r-fold SUMSET of mu_s |  = #{ distinct c : a_r(c) > 0 },
        a_r(c) = #{ (x_1,...,x_r) in mu_s^r : sum x_i = c }.       <- a SET CARDINALITY
  (B) additive energy   E_r := sum_c a_r(c)^2 = #{(x,y): sum x = sum y}.  <- a MOMENT (the 2r-th
        moment of the sup-norm via E_r = (1/p) sum_b |eta_b|^{2r}).

CLAIM TO TEST (part a): the EXACT identity
   E_r(F_p) = E_r(char-0) + Sigma_r,
   Sigma_r := #{ char-p-ONLY solutions of sum_{i=1}^r x_i = sum_{i=1}^r y_i in mu_s,
                 i.e. tuples equal mod p but NOT equal in Z[zeta_s] }.
We compute E_r over F_p AND over Z[zeta_s] (the ring) and verify E_r(F_p) - E_r(char0) = Sigma_r
by also DIRECTLY enumerating the char-p-only collisions.  Small n, several p.

CLAIM TO TEST (part b/core): is N0 (the count) q-INDEPENDENT and equal to its char-0 value
|H^{(+r)}| for p above a SMALL threshold, while E_r KEEPS GROWING / stays a moment?  i.e. does
the SET-CARDINALITY saturate (single-r, BGK-free) while the MOMENT does not?  This is the whole
question: if N0 saturates at small p but E_r is the moment, then delta* (which depends on N0)
bypasses the wall; if N0 ITSELF only saturates at p > exp(n), it re-hits the wall.

We measure, for fixed small mu_s, sweeping p == 1 mod s:
   N0(F_p)        = |sumset|         vs   N0_char0 = |H^{(+r)}|
   E_r(F_p)                          vs   E_r_char0
and the bad primes (where N0(F_p) != N0_char0).  The DECISIVE diagnostic: max bad prime for N0
vs the moment's char-p anomaly A_r = E_r(F_p) - E_r_char0 (which is the BGK object).
"""
import sys, itertools
from collections import Counter
from sympy import isprime, primitive_root


def primes_1modn(n, count, lo=None):
    out = []
    p = (lo or 1)
    p = p - (p % n) + 1
    if p <= (lo or 1):
        p += n
    while len(out) < count:
        if p > 2 and isprime(p):
            out.append(p)
        p += n
    return out


def fp_root(s, p):
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // s, p)


def sumset_and_energy_Fp(s, r, p):
    """N0 = |r-fold sumset|, E_r = additive energy, both over F_p, via convolution on exponents."""
    g = fp_root(s, p)
    roots = [pow(g, i, p) for i in range(s)]
    # r-fold autoconvolution: dist[c] = #tuples summing to c
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for c, m in dist.items():
            for v in roots:
                nd[(c + v) % p] += m
        dist = nd
    N0 = len(dist)
    Er = sum(m * m for m in dist.values())
    return N0, Er, dist


def sumset_and_energy_char0(s, r):
    """N0 and E_r in the ring Z[zeta_s]: represent zeta_s^i by exponent i in Z/s, but track the
    ACTUAL lattice vector.  Use the integral basis 1,z,...,z^{h-1}, z^h = -1 (h = s/2) for 2-power s.
    A root zeta^i -> standard basis vector e_{i mod h} with sign (-1)^{i//h}.  Sum is a length-h
    integer vector.  Distinct vectors = char-0 distinct sums."""
    assert s % 2 == 0
    h = s // 2

    def vec_of_root(i):
        col = i % h
        sgn = -1 if ((i // h) % 2) == 1 else 1
        return (col, sgn)

    # convolution over the lattice: key = tuple(length-h vector)
    start = tuple([0] * h)
    dist = Counter({start: 1})
    rootvecs = [vec_of_root(i) for i in range(s)]
    for _ in range(r):
        nd = Counter()
        for vkey, m in dist.items():
            for (col, sgn) in rootvecs:
                lst = list(vkey)
                lst[col] += sgn
                nd[tuple(lst)] += m
        dist = nd
    N0 = len(dist)
    Er = sum(m * m for m in dist.values())
    return N0, Er, dist


def main():
    print("=" * 92)
    print("C1 — bad-scalar COUNT (set cardinality) vs additive ENERGY (moment): saturation race")
    print("=" * 92)

    # part (a): verify E_r(F_p) = E_r(char0) + Sigma_r  exactly, with Sigma_r the char-p-only excess
    print("\n[part a] EXACT identity  E_r(F_p) = E_r(char0) + Sigma_r")
    print(f"{'s':>3} {'r':>2} {'p':>7} | {'Er_Fp':>9} {'Er_c0':>9} {'Sig=diff':>9} {'N0_Fp':>7} {'N0_c0':>7}")
    for s in [4, 8]:
        for r in [2, 3]:
            N0c0, Erc0, _ = sumset_and_energy_char0(s, r)
            for p in primes_1modn(s, 4):
                N0fp, Erfp, _ = sumset_and_energy_Fp(s, r, p)
                Sigma = Erfp - Erc0
                flag = "" if Erfp >= Erc0 else "  <<NEG?>>"
                print(f"{s:>3} {r:>2} {p:>7} | {Erfp:>9} {Erc0:>9} {Sigma:>9} {N0fp:>7} {N0c0:>7}{flag}")

    # part (b): the saturation RACE — does N0 reach char-0 value at SMALL p while E_r stays a moment?
    print("\n[part b] saturation race: N0(F_p) -> N0_char0 (set) vs A_r = E_r(F_p)-E_r_char0 (moment)")
    for s in [8, 16]:
        for r in [2, 3]:
            N0c0, Erc0, _ = sumset_and_energy_char0(s, r)
            print(f"\n  s={s} r={r}:  N0_char0=|H^(+r)|={N0c0}   E_r_char0={Erc0}")
            print(f"    {'p':>8} {'N0_Fp':>7} {'N0=c0?':>7} {'E_r_Fp':>10} {'A_r=anom':>9} {'A_r/Er0':>8}")
            badprimes = []
            for p in primes_1modn(s, 12):
                N0fp, Erfp, _ = sumset_and_energy_Fp(s, r, p)
                Ar = Erfp - Erc0
                eq = (N0fp == N0c0)
                if not eq:
                    badprimes.append(p)
                print(f"    {p:>8} {N0fp:>7} {str(eq):>7} {Erfp:>10} {Ar:>9} {Ar/Erc0:>8.3f}")
            print(f"    -> bad primes for the COUNT N0 (N0_Fp != N0_char0): {badprimes}")
            if badprimes:
                print(f"    -> max bad prime = {max(badprimes)}   (s^2={s*s}, s^3={s**3})")
            else:
                print(f"    -> NO bad prime in range: count saturated below smallest scanned prime")


if __name__ == "__main__":
    main()
