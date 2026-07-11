#!/usr/bin/env python3
"""
#444 probe — the char-0 Lam-Leung SLACK leading-coefficient law:

    Slack_r := (2r-1)!! * n^r - E_r(mu_n)  ~  c_r * n^{r-1},   c_r = C(r,2) * (2r-1)!!.

This probe verifies the law by an INDEPENDENT exact char-0 energy computation (roots-of-unity
sign-reduction), NOT from the in-tree closed-form polynomials. For G = mu_n = the n-th roots of
unity (char 0, n = 2^m so -1 in G), the char-0 additive energy

    E_r(mu_n) = #{ (a_1..a_r, b_1..b_r) in (Z/n)^{2r} : sum zeta^{a_i} = sum zeta^{b_j} }

is computed EXACTLY: for n = 2^m the minimal polynomial of zeta is x^{n/2}+1, so zeta^{k+n/2} = -zeta^k.
A Z-linear combination of n-th roots vanishes iff its reduced length-(n/2) coefficient vector is 0.
We count exactly via convolution over the half-basis, then polynomial-fit the n^{r-1} coefficient.

Verdict (committed alongside Frontier/CharZeroSlackLeadingCoeff.lean): the leading slack coefficient
c_r reproduces C(r,2)*(2r-1)!! at every accessible r, matching the in-tree _BchksF5 gap_* lemmas
(630, 9450, 155925, 2837835 for r=4,5,6,7) and the _CharZeroLamLeungSlackLower r=2,3 values (3, 45).

Run:  python3 scripts/probes/probe_slack_leading_coeff_law.py
"""
from collections import Counter
from fractions import Fraction
from math import comb


def doublefact_odd(k: int) -> int:
    p = 1
    i = k
    while i > 0:
        p *= i
        i -= 2
    return p


def Er_exact_2pow(n: int, r: int) -> int:
    """Exact char-0 additive energy E_r(mu_n), n = 2^m, via roots-of-unity sign reduction."""
    h = n // 2

    def red(k):
        k %= n
        return (k, 1) if k < h else (k - h, -1)

    singles = []
    for k in range(n):
        b, s = red(k)
        v = [0] * h
        v[b] = s
        singles.append(tuple(v))

    dist = Counter({tuple([0] * h): 1})
    for _ in range(r):
        nd = Counter()
        for vec, c in dist.items():
            for sv in singles:
                nv = tuple(a + b for a, b in zip(vec, sv))
                nd[nv] += c
        dist = nd
    return sum(c * c for c in dist.values())


def fit_poly(points):
    """Exact Lagrange/Vandermonde solve; returns coeffs high-degree -> low."""
    xs = [Fraction(x) for x, _ in points]
    ys = [Fraction(y) for _, y in points]
    N = len(points)
    A = [[x ** j for j in range(N - 1, -1, -1)] for x in xs]
    bb = ys[:]
    for i in range(N):
        p = A[i][i]
        if p == 0:
            for kk in range(i + 1, N):
                if A[kk][i] != 0:
                    A[i], A[kk] = A[kk], A[i]
                    bb[i], bb[kk] = bb[kk], bb[i]
                    break
            p = A[i][i]
        inv = Fraction(1) / p
        A[i] = [x * inv for x in A[i]]
        bb[i] *= inv
        for kk in range(N):
            if kk != i and A[kk][i] != 0:
                f = A[kk][i]
                A[kk] = [a - f * b for a, b in zip(A[kk], A[i])]
                bb[kk] -= f * bb[i]
    return bb


def main():
    print("# char-0 Lam-Leung slack leading-coefficient law: c_r = C(r,2)*(2r-1)!!")
    print("# (exact energy from roots-of-unity sign reduction; INDEPENDENT of in-tree polynomials)\n")
    all_ok = True
    for r in (2, 3, 4):
        pts = []
        for m in range(1, r + 3):
            n = 2 ** m
            pts.append((n, Er_exact_2pow(n, r)))
        coeffs = fit_poly(pts[: r + 1])
        lead = coeffs[0]          # n^r
        second = coeffs[1]        # n^{r-1}
        wick = doublefact_odd(2 * r - 1)
        slack_lead = wick - second  # Wick leading is wick at n^r, slack n^{r-1} coeff = -second
        # slack_r = Wick - E_r ; its n^{r-1} coeff = -(E_r's n^{r-1} coeff) = -second
        c_r_observed = -second
        c_r_law = comb(r, 2) * wick
        ok = (lead == wick) and (c_r_observed == c_r_law)
        all_ok = all_ok and ok
        print(f"r={r}: E_r leading (n^{r}) = {lead} (Wick (2r-1)!! = {wick}); "
              f"slack lead coeff c_r = {c_r_observed}; law C(r,2)*(2r-1)!! = {c_r_law}; "
              f"MATCH = {ok}")
    print("\n# prediction beyond the in-tree ladder (r=8,9,10):")
    for r in (8, 9, 10):
        print(f"  r={r}: c_r = C(r,2)*(2r-1)!! = {comb(r,2)*doublefact_odd(2*r-1)}")
    print(f"\nVERDICT: all accessible r match the law: {all_ok}")
    print("NOTE: this is char-0 headroom (Theta(n^{r-1})); the open (P2-Slack) residual "
          "Spur_r(p) <= Slack_r still needs the char-p spurious count = the BGK wall. NOT CORE.")


if __name__ == "__main__":
    main()
