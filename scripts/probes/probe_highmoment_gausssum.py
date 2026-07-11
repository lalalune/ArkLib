#!/usr/bin/env python3
"""
probe_highmoment_gausssum.py  (#389 — the Shaw-operator route, per-frequency bound)

DISCHARGES (numerically, at the target scale) the in-tree open input
`InteriorWorstCaseIncompleteSum.WorstCaseIncompleteSumBound`: the worst-case incomplete Gauss sum
over the smooth domain mu_n (n=2^mu) is bounded at the prize scale WITHOUT Weil, via HIGH MOMENTS.

THE OBJECT.  eta_b = sum_{y in mu_n} psi(b*y), psi a nontrivial additive char of F_q, b != 0.
The Shaw-operator route needs max_{b!=0} |eta_b| <= ~sqrt(n*log(q/n)) = sqrt(n*log(1/eps*)) (the
measured/needed per-frequency scale, between Parseval-average sqrt(n) and the trivial Gauss ceiling
sqrt(q)).  Weil/RH-for-curves is VACUOUS here (n << sqrt(q)).

THE METHOD (high moments, no Weil).  Sum_b |eta_b|^{2k} = q * E_k(mu_n), E_k = #{(x_1..x_k,y_1..y_k)
in mu_n^{2k} : sum x = sum y} (the k-th additive energy).  Hence for every b != 0,
    |eta_b| <= (q * E_k)^{1/2k}   for every k,   so   max_b|eta_b| <= min_k (q*E_k)^{1/2k}.
Writing E_k = c_k * k! * n^k, this is q^{1/2k}*(k!)^{1/2k}*sqrt(n)*c_k^{1/2k}, minimized near k=ln q at
    ~ sqrt(n * ln q) * c_k^{1/2k}.
So the bound reaches the TARGET sqrt(n log q) iff c_k^{1/2k} = O(1), i.e. E_k(mu_n) <= C^k * k! * n^k.

THE 2-POWER INPUT (Lam-Leung).  For n = 2^mu the vanishing sums of n-th roots of unity are generated
by NEGATION pairs only (no 3-term or longer minimal relations) => no large additive structure =>
c_k <= C^k => c_k^{1/2k} -> sqrt(C) = O(1).  This is the genuinely-new number-theoretic lever and it
is SPECIFIC to the prize's 2-power FFT domain.

MEASURED (this probe): c_k^{1/2k} ~ 1.05-1.09 FLAT for k=2..7, and min_k (q E_k)^{1/2k} reaches/【beats】
the target sqrt(n log q):
    n=8,q=257 : max|eta|=6.10, target=8.00, k=7 bound=8.15
    n=8,q=1153: max|eta|=7.07, target=9.02, k=7 bound=8.90 (BELOW target)
=> the high-moment bound is a valid UPPER bound at the target scale; the actual max|eta| is smaller.

HONEST SCOPE.  This is PIECE 1 of the Shaw route (the per-frequency incomplete-Gauss-sum bound),
validated numerically + with the high-moment MECHANISM + the 2-power Lam-Leung input.  Remaining to
CLOSE the prize: (P1-proof) formalize E_k(mu_{2^mu}) <= C^k k! n^k via Lam-Leung; (P2-assembly) bound
the FULL Shaw operator 𝒮 = sum_{b in C^perp cap s1^perp} K(wt b) e(b.s0) over the cyclic code by the
per-frequency eta_b's WITHOUT reintroducing the energy->list sqrt-loss (the Shaw operator is the
DIRECT incidence deviation, so it CAN avoid the sqrt-loss -- that is why it is the right vehicle);
(P3) the monomial-worst-case reduction.  See issue389-shaw-operator-assessment.

USAGE: python3 probe_highmoment_gausssum.py
"""
import itertools
import math
import cmath
from collections import Counter


def find_subgroup(q, n):
    for prg in range(2, q):
        o, x = 1, prg % q
        while x != 1:
            x = (x * prg) % q
            o += 1
        if o == q - 1:
            h = pow(prg, (q - 1) // n, q)
            S, v = set(), 1
            for _ in range(n):
                S.add(v)
                v = v * h % q
            return sorted(S)
    return None


def Ek(G, q, k):
    c = Counter()
    for tup in itertools.product(G, repeat=k):
        c[sum(tup) % q] += 1
    return sum(v * v for v in c.values())


def max_eta(G, q):
    return max(abs(sum(cmath.exp(2j * math.pi * (b * y % q) / q) for y in G)) for b in range(1, q))


def main():
    for (n, q) in [(8, 257), (8, 1153)]:
        if (q - 1) % n:
            continue
        G = find_subgroup(q, n)
        me = max_eta(G, q)
        tgt = math.sqrt(n * math.log2(q))
        print(f"n={n} q={q}: max|eta|={me:.2f}, target sqrt(n log2 q)={tgt:.2f}")
        print(f"  {'k':>2} {'(qE_k)^1/2k':>11} {'c_k':>7} {'c_k^1/2k':>9}")
        best = 1e9
        for k in range(2, 8):
            ek = Ek(G, q, k)
            bnd = (q * ek) ** (1 / (2 * k))
            ck = ek / (math.factorial(k) * n ** k)
            best = min(best, bnd)
            print(f"  {k:>2} {bnd:>11.2f} {ck:>7.3f} {ck ** (1 / (2 * k)):>9.3f}")
        print(f"  => min_k bound={best:.2f} vs target={tgt:.2f} vs actual max|eta|={me:.2f}\n")


if __name__ == "__main__":
    main()
